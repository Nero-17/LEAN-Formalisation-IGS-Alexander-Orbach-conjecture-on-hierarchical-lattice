"""Package this round's single authoritative report and source attachments."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import zipfile
import os
import sys

sys.stdout.reconfigure(encoding='utf-8')

root = Path(__file__).resolve().parents[1]
state_path = root / 'ROUND_STATE.json'
state = json.loads(state_path.read_text(encoding='utf-8'))
now = datetime.now(timezone.utc)
start = datetime.fromisoformat(state['startUtc'].replace('Z', '+00:00'))
elapsed = (now - start).total_seconds()
if elapsed < 1800:
    raise RuntimeError('This round has not yet passed the 30-minute archive threshold')
state['checkpointUtc'] = now.isoformat()
state['continuousWallSeconds'] = elapsed
state['manuscriptFormalisationComplete'] = False
state_path.write_text(json.dumps(state, indent=2, ensure_ascii=False), encoding='utf-8')

archive = root.parent / f"IGSIII-Section3-Lean_{state['round']}_完整研究记录.zip"
excluded_parts = {'.git', '.lake', '__pycache__', 'drafts'}
paths = []
for directory, subdirectories, filenames in os.walk(root, followlinks=False):
    subdirectories[:] = [name for name in subdirectories if name not in excluded_parts]
    for filename in filenames:
        path = Path(directory) / filename
        if path.suffix.lower() not in {'.zip', '.pdf', '.pyc'}:
            paths.append(path)
paths.sort()
contents = {str(path.relative_to(root)): path.read_bytes() for path in paths}
manifest = {relative: hashlib.sha256(content).hexdigest()
            for relative, content in contents.items()}
with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED) as output:
    for relative, content in contents.items():
        output.writestr(relative, content)
    output.writestr('ROUND_ARCHIVE_MANIFEST.json', json.dumps({
        'round': state['round'], 'createdUtc': now.isoformat(),
        'startUtc': state['startUtc'], 'continuousWallSeconds': elapsed,
        'completeSectionThree': False, 'sourceSha256': manifest,
        'note': 'This is an ongoing research snapshot. Consult RESEARCH_RECORD.md and COVERAGE.md; compile/audit certificates apply only to their recorded source hashes.'
    }, indent=2, ensure_ascii=False))
with zipfile.ZipFile(archive) as check:
    if check.testzip() is not None:
        raise RuntimeError('Archive failed ZIP integrity verification')
print(json.dumps({'archive': str(archive), 'size': archive.stat().st_size,
                  'files': len(paths), 'wallSeconds': elapsed}, ensure_ascii=False))
