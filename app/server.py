"""LTL 联锁复核 HTTP 服务（Python 标准库，零第三方依赖）。

路由：
  POST /checks                     提交复核；成功才分配编号并落审计，非法输入 400 且无审计
  GET  /checks/<id>                按编号读取成立结论或违规套索证据
  POST /checks/<id>/audits         对已判不成立的复核发起规范最短违规执行审计
  GET  /checks/<id>/audits         列出该复核的规范最短违规执行审计
  GET  /checks/<id>/audits/<aid>   读取审计详情（每步位置/切换/公平集命中证据）
  GET  /health                     健康检查

端口由环境变量 ``LTL_PORT`` 指定（默认 8080），数据目录由
``LTL_DATA_DIR`` 指定（默认 /data）。
"""

from __future__ import annotations

import json
import os
import re
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import Any, Dict, Optional

from .audit import (
    MAX_FAIRNESS_SETS,
    AuditInvariantError,
    FairnessLimitExceeded,
    build_audit,
)
from .checker import check, push_negation
from .storage import AuditStore
from .validation import ValidationError, validate_request

_MAX_BODY = 4 * 1024 * 1024
_ID_RE = re.compile(r"^/checks/([A-Za-z0-9_-]+)$")
_AUDITS_RE = re.compile(r"^/checks/([A-Za-z0-9_-]+)/audits$")
_AUDIT_RE = re.compile(r"^/checks/([A-Za-z0-9_-]+)/audits/([A-Za-z0-9_-]+)$")


def frozen_spec(spec: Dict[str, Any]) -> Dict[str, Any]:
    """可 JSON 化的冻结来源快照：规程（位置/切换/命题）、公式与初态。"""
    return {
        "locations": list(spec["locations"]),
        "initial": spec["initial"],
        "switches": [dict(sw) for sw in spec["switches"]],
        "propositions": {loc: list(ps)
                         for loc, ps in spec["propositions"].items()},
        "formula": spec["formula"],
    }


def build_record(spec: Dict[str, Any]) -> Dict[str, Any]:
    result = check(spec)
    neg_nnf = push_negation(spec["formula_ast"], neg=True)
    record: Dict[str, Any] = {
        "formula": spec["formula"],
        "initial": spec["initial"],
        "holds": result.holds,
        "normalization": {
            "negation_nnf": neg_nnf.to_str(),
            "method": "否定公式广义 Büchi 自动机（tableau）× 规程乘积 × 接受 SCC",
        },
        "stats": result.stats,
        "violation": result.violation,
        # 冻结来源规程、公式与初态，供规范最短违规执行审计原样复用
        "spec": frozen_spec(spec),
    }
    return record


class Handler(BaseHTTPRequestHandler):
    server_version = "LTLInterlock/1.0"

    # ---- 注入的共享件 ----
    store: AuditStore = None  # type: ignore[assignment]

    def log_message(self, fmt: str, *args: Any) -> None:
        # 结构化一行日志
        import datetime
        ts = datetime.datetime.now(datetime.timezone.utc).isoformat()
        print(f"[{ts}] {self.address_string()} {fmt % args}", flush=True)

    # ---- 工具 ----
    def _send_json(self, status: int, payload: Dict[str, Any]) -> None:
        body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _read_json(self) -> Optional[Dict[str, Any]]:
        try:
            length = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            self._send_json(400, {"error": "bad_request",
                                  "errors": ["Content-Length 非法"]})
            return None
        if length <= 0 or length > _MAX_BODY:
            self._send_json(400, {"error": "bad_request",
                                  "errors": ["请求体为空或超过 4MiB 限制"]})
            return None
        raw = self.rfile.read(length)
        try:
            payload = json.loads(raw.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            self._send_json(400, {"error": "bad_json",
                                  "errors": [f"JSON 解析失败: {exc}"]})
            return None
        if not isinstance(payload, dict):
            self._send_json(400, {"error": "bad_request",
                                  "errors": ["请求体必须是 JSON 对象"]})
            return None
        return payload

    def _drain_body(self) -> None:
        """丢弃随请求带来的请求体（审计只使用冻结快照，不读新输入）。"""
        try:
            length = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            return
        if 0 < length <= _MAX_BODY:
            self.rfile.read(length)

    # ---- 路由 ----
    def do_GET(self) -> None:  # noqa: N802
        path = self.path.split("?", 1)[0]
        if path == "/health":
            self._send_json(200, {"status": "ok"})
            return
        m = _AUDIT_RE.match(path)
        if m:
            check_id, audit_id = m.groups()
            record = self.store.get_audit(audit_id)
            if record is None or record.get("check_id") != check_id:
                self._send_json(404, {
                    "error": "not_found",
                    "errors": [f"审计编号 {audit_id} 在复核 {check_id} 下不存在"],
                })
                return
            self._send_json(200, record)
            return
        m = _AUDITS_RE.match(path)
        if m:
            check_id = m.group(1)
            if self.store.get(check_id) is None:
                self._send_json(404, {"error": "not_found",
                                      "errors": [f"编号 {check_id} 不存在"]})
                return
            audits = [{
                "id": a["id"],
                "check_id": a["check_id"],
                "fairness_set_count": a.get("fairness_set_count"),
                "total_switches": a.get("canonical_lasso", {})
                                      .get("total_switches"),
            } for a in self.store.list_audits(check_id)]
            self._send_json(200, {"check_id": check_id, "audits": audits})
            return
        m = _ID_RE.match(path)
        if m:
            record = self.store.get(m.group(1))
            if record is None:
                self._send_json(404, {"error": "not_found",
                                      "errors": [f"编号 {m.group(1)} 不存在"]})
                return
            self._send_json(200, record)
            return
        self._send_json(404, {"error": "not_found", "errors": ["未知路径"]})

    def do_POST(self) -> None:  # noqa: N802
        path = self.path.split("?", 1)[0]
        if path == "/checks":
            self._handle_create_check()
            return
        m = _AUDITS_RE.match(path)
        if m:
            self._handle_create_audit(m.group(1))
            return
        self._send_json(404, {"error": "not_found", "errors": ["未知路径"]})

    # ---- 复核 ----
    def _handle_create_check(self) -> None:
        payload = self._read_json()
        if payload is None:
            return
        try:
            spec = validate_request(payload)
        except ValidationError as exc:
            # 非法输入：定位拒绝，不生成审计编号
            self._send_json(400, {
                "error": "validation_failed",
                "errors": exc.errors,
            })
            return
        try:
            record = build_record(spec)
        except Exception as exc:  # 检测器内部错误不应吞掉
            self._send_json(500, {"error": "checker_fault",
                                  "errors": [f"{type(exc).__name__}: {exc}"]})
            return
        audit_id = self.store.save(record)
        record_out = {"id": audit_id, **record}
        self._send_json(201, record_out)

    # ---- 规范最短违规执行审计 ----
    def _handle_create_audit(self, check_id: str) -> None:
        self._drain_body()
        record = self.store.get(check_id)
        if record is None:
            # 缺失编号：明确拒绝，不新增审计
            self._send_json(404, {"error": "not_found",
                                  "errors": [f"编号 {check_id} 不存在"]})
            return
        if record.get("holds") is not False:
            # 来源成立：明确拒绝，不新增审计
            self._send_json(409, {
                "error": "source_holds",
                "errors": [
                    f"复核 {check_id} 结论为成立（holds=true），规范最短违规"
                    "执行审计仅适用于判定不成立的复核，未新增审计"
                ],
            })
            return
        frozen = record.get("spec")
        if not isinstance(frozen, dict):
            self._send_json(409, {
                "error": "frozen_spec_unavailable",
                "errors": [
                    f"复核 {check_id} 缺少冻结的来源规程快照，无法发起审计"
                ],
            })
            return
        try:
            spec = validate_request(frozen)
        except ValidationError as exc:
            self._send_json(500, {
                "error": "frozen_spec_invalid",
                "errors": [f"冻结快照不再通过校验: {e}" for e in exc.errors],
            })
            return
        original_total = None
        viol = record.get("violation")
        if isinstance(viol, dict):
            pl, cl = viol.get("prefix_length"), viol.get("cycle_length")
            if isinstance(pl, int) and isinstance(cl, int):
                original_total = pl + cl
        try:
            audit = build_audit(spec, original_total)
        except FairnessLimitExceeded as exc:
            # 公平集超过该审计可处理上限：明确拒绝，不新增审计
            self._send_json(422, {
                "error": "fairness_limit_exceeded",
                "errors": [
                    f"否定公式产生 {exc.count} 个公平集，超过该审计可处理"
                    f"上限 {MAX_FAIRNESS_SETS}，未新增审计"
                ],
            })
            return
        except AuditInvariantError as exc:
            self._send_json(500, {"error": "audit_fault",
                                  "errors": [str(exc)]})
            return
        audit_id = self.store.save_audit(check_id, audit)
        self._send_json(201, {"id": audit_id, "check_id": check_id, **audit})


def create_server(host: str, port: int, data_dir: str) -> ThreadingHTTPServer:
    store = AuditStore(data_dir)
    handler = type("BoundHandler", (Handler,), {"store": store})
    httpd = ThreadingHTTPServer((host, port), handler)
    httpd.daemon_threads = True
    return httpd


def main() -> None:
    host = os.environ.get("LTL_HOST", "0.0.0.0")
    port = int(os.environ.get("LTL_PORT", "8080"))
    data_dir = os.environ.get("LTL_DATA_DIR", "/data")
    httpd = create_server(host, port, data_dir)
    print(f"LTL 联锁复核服务监听 {host}:{port}，数据目录 {data_dir}", flush=True)
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        httpd.server_close()


if __name__ == "__main__":
    main()
