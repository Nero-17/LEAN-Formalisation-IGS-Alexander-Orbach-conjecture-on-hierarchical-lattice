"""Update this continuous round's single local ZIP; never traverse package junctions."""
from pathlib import Path
import hashlib
import json
import os
import zipfile

root = Path(__file__).resolve().parents[1]
archive = root.parent / 'IGSIII-Sections3-4-Lean_2026-10-10-010601_完整研究记录.zip'
paths = []
for current, directories, files in os.walk(root, topdown=True, followlinks=False):
    directories[:] = [name for name in directories if name not in {'.lake', '.git', '__pycache__'}]
    for name in files:
        if name != 'Probe.lean' and not name.endswith('Draft.lean'):
            paths.append(Path(current) / name)
with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED) as output:
    for path in sorted(paths):
        output.write(path, str(path.relative_to(root)))
with zipfile.ZipFile(archive) as check:
    assert check.testzip() is None
print(json.dumps({'path': str(archive), 'files': len(paths),
                  'bytes': archive.stat().st_size,
                  'sha256': hashlib.sha256(archive.read_bytes()).hexdigest()}, ensure_ascii=False))
