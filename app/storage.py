"""复核审计的持久化存储（JSON 文件，线程安全）。

复核成功后保存编号与结论；非法请求在校验阶段即被拒绝，不生成编号、不落审计。
"""

from __future__ import annotations

import json
import os
import threading
from typing import Any, Dict, List, Optional


class AuditStore:
    def __init__(self, data_dir: str):
        self.data_dir = data_dir
        self.path = os.path.join(data_dir, "audit.json")
        self._lock = threading.Lock()
        os.makedirs(data_dir, exist_ok=True)
        if not os.path.exists(self.path):
            self._write_locked({"seq": 0, "records": {}})

    def _write_locked(self, data: Dict[str, Any]) -> None:
        tmp = self.path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as fh:
            json.dump(data, fh, ensure_ascii=False, indent=2)
        os.replace(tmp, self.path)

    def _read(self) -> Dict[str, Any]:
        with open(self.path, "r", encoding="utf-8") as fh:
            return json.load(fh)

    def save(self, record: Dict[str, Any]) -> str:
        """保存一条复核记录，返回分配的审计编号。"""
        with self._lock:
            data = self._read()
            data["seq"] += 1
            audit_id = f"CHK-{data['seq']:06d}"
            record = {"id": audit_id, **record}
            data["records"][audit_id] = record
            self._write_locked(data)
        return audit_id

    def get(self, audit_id: str) -> Optional[Dict[str, Any]]:
        with self._lock:
            return self._read()["records"].get(audit_id)

    def list_ids(self) -> List[str]:
        with self._lock:
            ids = list(self._read()["records"].keys())
        return sorted(ids)
