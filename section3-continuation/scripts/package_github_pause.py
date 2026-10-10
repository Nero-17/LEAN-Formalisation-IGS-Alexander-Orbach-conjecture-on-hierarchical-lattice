"""Preserve the existing package and all continuation Lean sources at user pause."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import shutil

source = Path(__file__).resolve().parent.parent
previous = Path('C:/Users/lzysh/Documents/Codex/2026-09-05/new-chat-2/outputs/LEAN-Formalisation-IGS-Alexander-Orbach-conjecture-on-hierarchical-lattice')
destination = source.parent / 'igs-iii-github-upload-20261010'
if destination.exists():
    raise RuntimeError('Destination already exists; inspect before updating')
shutil.copytree(previous, destination, ignore=shutil.ignore_patterns('.lake', '__pycache__'))
continuation = destination / 'section3-continuation'
continuation.mkdir()
excluded_directories = {'.git', '.lake', '__pycache__', 'paper'}
excluded_files = {'00_最新进展.md', 'RESEARCH_RECORD.md', 'ROUND_STATE.json'}
for directory, children, names in os.walk(source, followlinks=False):
    children[:] = [name for name in children if name not in excluded_directories]
    for name in names:
        path = Path(directory) / name
        if name in excluded_files or path.suffix.lower() in {'.zip', '.pdf', '.pyc', '.olean', '.ilean'}:
            continue
        relative = path.relative_to(source)
        target = continuation / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, target)
inventory = {}
for directory, children, names in os.walk(destination, followlinks=False):
    children[:] = [name for name in children if name not in {'.git', '.lake'}]
    for name in names:
        path = Path(directory) / name
        if path.suffix == '.lean':
            inventory[path.relative_to(destination).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
manifest = {
    'createdUtc': datetime.now(timezone.utc).isoformat(),
    'reason': 'User requested pause and upload of all existing Lean code',
    'baseCommit': '28d73af',
    'section3Complete': False,
    'containsUnverifiedWorkingDrafts': True,
    'auditedContinuationDeclarationCount': 5646,
    'auditScope': 'section3-continuation/verification/manifest.json, recorded source hashes only',
    'leanSourceCount': len(inventory),
    'leanSourceSha256': dict(sorted(inventory.items())),
}
(destination / 'PAUSED_SNAPSHOT.json').write_text(json.dumps(manifest, indent=2, ensure_ascii=False), encoding='utf-8')
readme = destination / 'README.md'
original = readme.read_text(encoding='utf-8')
notice = '''# Paused Lean snapshot — 2026-10-10

The user paused formalisation and requested preservation of all existing Lean code.
The original Sections 2–4 package below is preserved. The newer independent
Section 3 project is included in **section3-continuation/**, with its pinned
dependencies, vendored sources, verification scripts and all working drafts.

**Section 3 remains incomplete.** Its last successful aggregate audit covers
5,646 declarations; the exact source hashes and scope are recorded in
section3-continuation/verification/manifest.json. Additional individually
compiled modules and unverified drafts are also preserved. A file being
present in this snapshot does not mean it compiled or belongs to the audit.
See section3-continuation/COVERAGE.md and PAUSED_SNAPSHOT.json.

To check the audited continuation closure, from section3-continuation/ run
`python scripts/verify.py --imported-only` after installing the pinned Lean
toolchain and fetching dependencies. This snapshot is a packaging operation;
it does not claim a fresh combined build or completed Section 3 proof.

---

'''
readme.write_text(notice + original, encoding='utf-8')
print(json.dumps({'destination': str(destination), 'leanSourceCount': len(inventory)}, ensure_ascii=False))
