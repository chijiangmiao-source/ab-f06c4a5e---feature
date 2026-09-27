#!/usr/bin/env python3
"""容器健康检查：访问 /health，status==ok 才退出 0。"""
import json
import os
import sys
import urllib.request

port = os.environ.get("LTL_PORT", "8080")
try:
    with urllib.request.urlopen(f"http://127.0.0.1:{port}/health", timeout=2) as r:
        body = json.load(r)
    sys.exit(0 if body.get("status") == "ok" else 1)
except Exception:
    sys.exit(1)
