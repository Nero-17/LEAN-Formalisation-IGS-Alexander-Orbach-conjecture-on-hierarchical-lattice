"""Freeze only the innovation-tree source import closure, without modifying its source project."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re

root = Path(__file__).resolve().parents[1]
source = Path('C:/Users/lzysh/Documents/Codex/2026-10-09/new-chat/outputs/igs-iii-lean')
sources = {}

def visit(module):
    if module in sources or not module.startswith('IGSIII.'):
        return
    relative = Path(module.replace('.', '/') + '.lean')
    content = (source / relative).read_bytes()
    sources[module] = (relative, content)
    for dependency in re.findall(r'^import\s+(\S+)', content.decode('utf-8'), re.M):
        visit(dependency)

roots = ['IGSIII.Probability.IndependentTreeChildren',
         'IGSIII.Chemical.SubstitutionPaths.InnovationCylinders']
for module in roots:
    visit(module)
for relative, content in sources.values():
    if (source / relative).read_bytes() != content:
        raise RuntimeError(f'Source changed during capture: {relative}')
for relative, content in sources.values():
    destination = root / relative
    if destination.exists() and destination.read_bytes() != content:
        raise RuntimeError(f'Refusing to overwrite a changed local snapshot: {relative}')
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(content)

manifest = {
    'capturedUtc': datetime.now(timezone.utc).isoformat(),
    'sourceProject': str(source),
    'rootModules': roots,
    'scope': 'Minimal source closure only; not a claim that the live Section 2 project is complete.',
    'rebuiltLocally': 'Compile and audit these source files with scripts/verify.py; no Section 2 object cache is copied.',
    'sourceSha256': {str(relative): hashlib.sha256(content).hexdigest()
                     for relative, content in sorted(sources.values())},
}
(root / 'SECTION2_SOURCE_MANIFEST.json').write_text(json.dumps(manifest, indent=2), encoding='utf-8')
print(json.dumps({'capturedModules': len(sources), 'sourceProjectUnmodified': True}))
