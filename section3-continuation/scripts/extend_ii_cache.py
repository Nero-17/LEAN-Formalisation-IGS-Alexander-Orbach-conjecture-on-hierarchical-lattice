"""Copy only missing pinned II compiled dependencies into this project's independent cache."""
from pathlib import Path
import hashlib
import json
import re
import shutil

root = Path(__file__).resolve().parents[1]
target = root / 'vendor/Universality'
source = Path('C:/Users/lzysh/Documents/Codex/2026-10-09/new-chat/outputs/igs-iii-lean/vendor/Universality')
manifest_path = target / 'CACHE_MANIFEST.json'
manifest = json.loads(manifest_path.read_text(encoding='utf-8'))
modules = set(manifest['modules'])
copied = []
visited = set()

def visit(module):
    if module in visited or not module.startswith('Universality.'):
        return
    visited.add(module)
    relative = Path(module.replace('.', '/') + '.lean')
    local_source = target / relative
    if local_source.read_bytes() != (source / relative).read_bytes():
        raise RuntimeError(f'Pinned II source mismatch: {module}')
    for dependency in re.findall(r'^import\s+(\S+)', local_source.read_text(encoding='utf-8'), re.M):
        visit(dependency)
    if module in modules:
        return
    stem = Path(module.replace('.', '/'))
    cache = source / '.lake/build/lib/lean'
    artifacts = list((cache / stem.parent).glob(stem.name + '.olean*'))
    if not (cache / stem.with_suffix('.olean')).exists():
        raise RuntimeError(f'Missing source II object: {module}')
    for artifact in artifacts:
        destination = target / '.lake/build/lib/lean' / artifact.relative_to(cache)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(artifact, destination)
        copied.append({'path': str(destination.relative_to(target)),
                       'sha256': hashlib.sha256(destination.read_bytes()).hexdigest()})
    modules.add(module)

for folder in ('IGSIII34', 'IGSIII'):
    for path in (root / folder).rglob('*.lean'):
        for dependency in re.findall(r'^import\s+(\S+)', path.read_text(encoding='utf-8'), re.M):
            visit(dependency)
manifest['modules'] = sorted(modules)
manifest.setdefault('extensions', []).append({'sourceProjectUnmodified': True, 'copiedArtifacts': copied})
manifest_path.write_text(json.dumps(manifest, indent=2), encoding='utf-8')
print(json.dumps({'totalIIModules': len(modules), 'newArtifacts': len(copied), 'reusedNotRebuilt': True}))
