"""HTTP 接口测试：编号存取、非法请求不生成审计、健康检查。"""

import json
import tempfile
import threading
import unittest
import urllib.error
import urllib.request
from http.server import ThreadingHTTPServer

from app.server import create_server


VALID_PAYLOAD = {
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


class ServerTestBase(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.httpd = create_server("127.0.0.1", 0, self.tmp.name)
        self.port = self.httpd.server_address[1]
        self.thread = threading.Thread(target=self.httpd.serve_forever,
                                       daemon=True)
        self.thread.start()

    def tearDown(self):
        self.httpd.shutdown()
        self.httpd.server_close()
        self.thread.join(timeout=5)
        self.tmp.cleanup()

    def url(self, path):
        return f"http://127.0.0.1:{self.port}{path}"

    def request(self, method, path, payload=None):
        data = None
        headers = {}
        if payload is not None:
            data = json.dumps(payload).encode("utf-8")
            headers["Content-Type"] = "application/json"
        req = urllib.request.Request(self.url(path), data=data,
                                     headers=headers, method=method)
        try:
            with urllib.request.urlopen(req, timeout=5) as resp:
                return resp.status, json.loads(resp.read().decode("utf-8"))
        except urllib.error.HTTPError as exc:
            return exc.code, json.loads(exc.read().decode("utf-8"))


class TestHttpApi(ServerTestBase):
    def test_health(self):
        status, body = self.request("GET", "/health")
        self.assertEqual(status, 200)
        self.assertEqual(body["status"], "ok")

    def test_create_and_read_holds(self):
        status, body = self.request("POST", "/checks", VALID_PAYLOAD)
        self.assertEqual(status, 201)
        self.assertTrue(body["holds"])
        self.assertIn("id", body)
        audit_id = body["id"]
        status2, fetched = self.request("GET", f"/checks/{audit_id}")
        self.assertEqual(status2, 200)
        self.assertEqual(fetched["id"], audit_id)
        self.assertTrue(fetched["holds"])
        self.assertIn("normalization", fetched)
        self.assertIn("negation_nnf", fetched["normalization"])

    def test_violation_returns_lasso(self):
        payload = json.loads(json.dumps(VALID_PAYLOAD))
        # 制造迟发闭环：req 可以不经过 grant 直接回 idle
        payload["locations"].append("archive")
        payload["switches"] = [
            {"id": "t1", "source": "idle", "target": "req"},
            {"id": "t2", "source": "req", "target": "idle"},
            {"id": "t3", "source": "req", "target": "grant"},
            {"id": "t4", "source": "grant", "target": "idle"},
            {"id": "t5", "source": "archive", "target": "archive"},
        ]
        payload["propositions"]["archive"] = ["granted"]
        status, body = self.request("POST", "/checks", payload)
        self.assertEqual(status, 201)
        self.assertFalse(body["holds"])
        v = body["violation"]
        self.assertGreaterEqual(v["cycle_length"], 1)
        for step in v["steps"]:
            self.assertIn("location", step)
            self.assertIn("switch_taken", step)
            self.assertIn("subformula_truth", step)

    def test_invalid_request_no_audit_created(self):
        # 死端
        bad = json.loads(json.dumps(VALID_PAYLOAD))
        bad["switches"] = [
            {"id": "t1", "source": "idle", "target": "req"},
            {"id": "t2", "source": "req", "target": "grant"},
            # grant 无外出
        ]
        status, body = self.request("POST", "/checks", bad)
        self.assertEqual(status, 400)
        self.assertTrue(any("死端" in e for e in body["errors"]))
        self.assertNotIn("id", body)

        # 悬空端点
        bad2 = json.loads(json.dumps(VALID_PAYLOAD))
        bad2["switches"][0]["target"] = "nowhere"
        status2, body2 = self.request("POST", "/checks", bad2)
        self.assertEqual(status2, 400)
        self.assertTrue(any("悬空端点" in e for e in body2["errors"]))

        # 非法公式
        bad3 = json.loads(json.dumps(VALID_PAYLOAD))
        bad3["formula"] = "request U granted"
        status3, body3 = self.request("POST", "/checks", bad3)
        self.assertEqual(status3, 400)

        # 审计存储仍为空
        # （成功创建一条后编号应从 CHK-000001 开始，证明此前无记录）
        status4, ok = self.request("POST", "/checks", VALID_PAYLOAD)
        self.assertEqual(ok["id"], "CHK-000001")

    def test_bad_json(self):
        req = urllib.request.Request(
            self.url("/checks"), data=b"{not json",
            headers={"Content-Type": "application/json"}, method="POST")
        try:
            urllib.request.urlopen(req, timeout=5)
            self.fail("应返回 400")
        except urllib.error.HTTPError as exc:
            self.assertEqual(exc.code, 400)

    def test_unknown_id_404(self):
        status, _ = self.request("GET", "/checks/CHK-999999")
        self.assertEqual(status, 404)


if __name__ == "__main__":
    unittest.main()
