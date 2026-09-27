#!/usr/bin/env python3
"""Compose verify 服务入口：

1. 构建检查：全部源码可编译（字节码语法检查）；
2. 代码测试：unittest 全量用例（含永不放行违规闭环检测）；
3. HTTP 冒烟：健康检查、成立结论、违规闭环证据、非法请求 400 且无审计、
   编号读取；
4. 规范最短违规执行审计：对违规复核发起最短化（总切换数不劣于原任意
   套索、闭环非空、每步公平集命中证据、按编号可读、来源不被改写），
   来源成立 409 / 编号缺失 404 / 公平集超限 422 且均不新增审计。

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

# 否定 NNF 为 F!a1 | ... | F!a7：7 个公平集，超过最短审计上限 6
SEVEN_FAIRNESS = {
    "locations": ["a", "b"],
    "initial": "a",
    "switches": [
        {"id": "ab", "source": "a", "target": "b"},
        {"id": "ba", "source": "b", "target": "a"},
    ],
    "propositions": {
        "a": [],
        "b": ["a1", "a2", "a3", "a4", "a5", "a6", "a7"],
    },
    "formula": "G a1 & G a2 & G a3 & G a4 & G a5 & G a6 & G a7",
}


def next_id(audit_id):
    prefix, num = audit_id.rsplit("-", 1)
    return f"{prefix}-{int(num) + 1:06d}"


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

    # ---- 规范最短违规执行审计 ----
    section("规范最短违规执行审计")
    status, body = http("POST", "/checks", STARVATION)
    src_id = body.get("id")
    src_v = body.get("violation") or {}
    src_total = src_v.get("prefix_length", 0) + src_v.get("cycle_length", 0)
    check("审计来源（违规闭环）创建 201 且 holds=false",
          status == 201 and body.get("holds") is False and src_id)

    status, audit = http("POST", f"/checks/{src_id}/shortest-violation")
    av = audit.get("violation") or {}
    asteps = av.get("steps", [])
    am = av.get("loop_start_index")
    acov = av.get("fairness_coverage", [])
    check("最短违规审计 201 且引用来源",
          status == 201 and audit.get("holds") is False
          and audit.get("source_check_id") == src_id and audit.get("id"))
    check("最短套索闭环非空且不劣于原任意套索",
          av.get("cycle_length", 0) >= 1
          and av.get("total_switches", 10**9) <= src_total)
    check("审计每步含位置/切换/公平集命中证据",
          bool(asteps) and all(
              isinstance(s.get("location"), str)
              and s.get("switch_taken")
              and isinstance(s.get("fairness_sets_hit"), list)
              for s in asteps))
    check("每个公平集均在闭环内命中",
          bool(acov) and am is not None and all(
              any(isinstance(i, int) and am <= i < len(asteps)
                  for i in c.get("hit_step_indices", []))
              for c in acov))
    check("最短闭环上公式逐点为假（无限违规）",
          am is not None
          and all(s.get("formula_true_here") is False for s in asteps[am:]))
    check("审计可按编号读取且来源复核不被改写",
          bool(audit.get("id"))
          and http("GET", f"/checks/{audit['id']}")[0] == 200
          and http("GET", f"/checks/{src_id}")[1]
          .get("violation", {}).get("kind") == "lasso")

    status, ok_body = http("POST", "/checks", COMPLIANT)
    ok_id2 = ok_body.get("id")
    status, body = http("POST", f"/checks/{ok_id2}/shortest-violation")
    check("来源成立拒绝审计 409 且不新增审计",
          status == 409 and "id" not in body)

    status, body = http("POST", "/checks/CHK-000000/shortest-violation")
    check("缺失编号拒绝审计 404", status == 404)

    status, seven = http("POST", "/checks", SEVEN_FAIRNESS)
    seven_id = seven.get("id")
    check("七公平集违规复核本身仍可判定",
          status == 201 and seven.get("holds") is False
          and seven.get("stats", {}).get("fairness_sets") == 7)
    status, body = http("POST", f"/checks/{seven_id}/shortest-violation")
    check("公平集超限拒绝审计 422 且不新增审计",
          status == 422 and body.get("error") == "fairness_limit_exceeded"
          and "id" not in body)
    status, tail = http("POST", "/checks", COMPLIANT)
    check("各项拒绝均未占用审计编号",
          status == 201 and bool(seven_id)
          and tail.get("id") == next_id(seven_id))

    section("汇总")
    if FAILURES:
        print(f"verify 失败 {len(FAILURES)} 项：{FAILURES}", flush=True)
        sys.exit(1)
    print("verify 全部通过，退出码 0", flush=True)
    sys.exit(0)


if __name__ == "__main__":
    main()
