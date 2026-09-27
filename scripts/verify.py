#!/usr/bin/env python3
"""Compose verify 服务入口：

1. 构建检查：全部源码可编译（字节码语法检查）；
2. 代码测试：unittest 全量用例（含永不放行违规闭环检测）；
3. HTTP 冒烟：健康检查、成立结论、违规闭环证据、非法请求 400 且无审计、编号读取。

任一步失败即以非零退出码退出。
"""
import json
import os
import py_compile
import sys
import unittest
import urllib.error
import urllib.request

BASE = os.environ.get("LTL_BASE_URL", "http://ltl:8080")
FAILURES = []


def section(title):
    print(f"\n=== {title} ===", flush=True)


def check(name, cond, detail=""):
    mark = "PASS" if cond else "FAIL"
    print(f"[{mark}] {name}{(' — ' + detail) if detail and not cond else ''}",
          flush=True)
    if not cond:
        FAILURES.append(name)


def http(method, path, payload=None):
    data = None
    headers = {}
    if payload is not None:
        data = json.dumps(payload).encode("utf-8")
        headers["Content-Type"] = "application/json"
    req = urllib.request.Request(BASE + path, data=data, headers=headers,
                                 method=method)
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            return resp.status, json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        return exc.code, json.loads(exc.read().decode("utf-8"))


# 永不放行（饥饿）闭环：request 出现后可不经 granted 直接返回
STARVATION = {
    "locations": ["idle", "req", "deny", "grant"],
    "initial": "idle",
    "switches": [
        {"id": "t1", "source": "idle", "target": "req"},
        {"id": "t2", "source": "req", "target": "idle"},
        {"id": "t3", "source": "req", "target": "deny"},
        {"id": "t4", "source": "deny", "target": "idle"},
        {"id": "tg", "source": "grant", "target": "idle"},
    ],
    "propositions": {
        "idle": [],
        "req": ["request"],
        "deny": ["denied"],
        "grant": ["granted"],
    },
    "formula": "G(!request | F granted)",
}

COMPLIANT = {
    "locations": ["idle", "req", "grant"],
    "initial": "idle",
    "switches": [
        {"id": "t1", "source": "idle", "target": "req"},
        {"id": "t2", "source": "req", "target": "grant"},
        {"id": "t3", "source": "grant", "target": "idle"},
    ],
    "propositions": {"idle": [], "req": ["request"],
                     "grant": ["request", "granted"]},
    "formula": "G(!request | F granted)",
}


def main():
    # 1. 构建检查
    section("构建检查 py_compile")
    compile_ok = True
    app_dir = os.path.join(os.path.dirname(__file__), "..", "app")
    for name in sorted(os.listdir(app_dir)):
        if name.endswith(".py"):
            path = os.path.join(app_dir, name)
            try:
                py_compile.compile(path, doraise=True)
                print(f"[PASS] compile {name}", flush=True)
            except py_compile.PyCompileError as exc:
                compile_ok = False
                print(f"[FAIL] compile {name}: {exc}", flush=True)
    check("全部源码编译通过", compile_ok)

    # 2. 代码测试
    section("代码测试 unittest")
    root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    sys.path.insert(0, root)
    loader = unittest.TestLoader()
    suite = loader.discover(os.path.join(root, "tests"), top_level_dir=root)
    runner = unittest.TextTestRunner(verbosity=1)
    result = runner.run(suite)
    check("单元测试全部通过", result.wasSuccessful(),
          f"{len(result.failures)+len(result.errors)} 个失败")

    # 3. HTTP 冒烟
    section("HTTP 冒烟")
    status, body = http("GET", "/health")
    check("GET /health 200 ok", status == 200 and body.get("status") == "ok",
          f"status={status}")

    status, body = http("POST", "/checks", COMPLIANT)
    ok_id = body.get("id")
    check("合规规程 POST /checks 201 且 holds=true",
          status == 201 and body.get("holds") is True and ok_id,
          f"status={status} body={body}")

    status, body = http("GET", f"/checks/{ok_id}")
    check("按编号读取成立结论",
          status == 200 and body.get("id") == ok_id
          and body.get("holds") is True,
          f"status={status}")
    check("记录含否定 NNF 与自动机方法说明",
          "negation_nnf" in body.get("normalization", {}),
          str(body.get("normalization")))

    status, body = http("POST", "/checks", STARVATION)
    v = body.get("violation") or {}
    steps = v.get("steps", [])
    m = v.get("loop_start_index")
    loop_locs = [s.get("location") for s in steps[m:]] if m is not None else []
    loop_false = all(s.get("formula_true_here") is False
                     for s in steps[m:]) if m is not None else False
    evidence_ok = all(
        isinstance(s.get("subformula_truth"), dict)
        and s.get("switch_taken") for s in steps
    )
    check("永不放行违规闭环 POST 201 且 holds=false",
          status == 201 and body.get("holds") is False and v,
          f"status={status}")
    check("闭环经过 request 且不经过 granted",
          "req" in loop_locs and "grant" not in loop_locs,
          f"loop_locs={loop_locs}")
    check("闭环上公式逐点为假（无限违规，非有限回放）", loop_false)
    check("每步含位置/切换/子式真值证据", evidence_ok)
    check("违规同样保存并可按编号读取",
          body.get("id") and http("GET", f"/checks/{body['id']}")[0] == 200)

    bad = json.loads(json.dumps(STARVATION))
    bad["switches"] = bad["switches"][:2]  # deny/grant 变死端
    status, body = http("POST", "/checks", bad)
    check("死端请求 400 且不分配编号",
          status == 400 and "id" not in body
          and any("死端" in e for e in body.get("errors", [])),
          f"status={status} body={body}")

    bad2 = json.loads(json.dumps(COMPLIANT))
    bad2["switches"][0]["target"] = "ghost"
    status, body = http("POST", "/checks", bad2)
    check("悬空端点 400 定位拒绝",
          status == 400 and any("悬空端点" in e for e in body.get("errors", [])))

    bad3 = json.loads(json.dumps(COMPLIANT))
    bad3["formula"] = "request U granted"
    status, body = http("POST", "/checks", bad3)
    check("非法公式 400 定位拒绝", status == 400)

    status, body = http("GET", "/checks/CHK-000000")
    check("不存在编号 404", status == 404)

    section("汇总")
    if FAILURES:
        print(f"verify 失败 {len(FAILURES)} 项：{FAILURES}", flush=True)
        sys.exit(1)
    print("verify 全部通过，退出码 0", flush=True)
    sys.exit(0)


if __name__ == "__main__":
    main()
