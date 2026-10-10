"""Snapshot the completed, audited Section 2 dependency; never write its live project."""
from pathlib import Path
import hashlib
import json
import shutil
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
SOURCE = Path('C:/Users/lzysh/Documents/Codex/2026-10-09/new-chat/outputs/igs-iii-lean')

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

manifest = json.loads((SOURCE / 'verification/manifest.json').read_text(encoding='utf-8-sig'))
state = json.loads((SOURCE / '.lake/igsiii-build-state.json').read_text(encoding='utf-8-sig'))
assert manifest['auditedDeclarations'] == 3318
assert manifest['sourceCommit'] == 'f0c4804685ad6aed415ac4f69926dff71960d641'
assert manifest['leanToolchain'] == (ROOT / 'lean-toolchain').read_text().strip()
assert manifest['mathlibRevision'] == '520045ab14e26149ee970e2e617ca04b09bde5d6'
records = []
for relative, expected in manifest['sourceSha256'].items():
    relative = Path(relative)
    original = SOURCE / relative
    module = '.'.join(relative.with_suffix('').parts)
    original_object = SOURCE / '.lake/build/lib/lean' / relative.with_suffix('.olean')
    assert digest(original) == expected.lower(), relative
    assert digest(original) == state[module]['source'].lower(), relative
    assert digest(original_object) == state[module]['object'].lower(), relative
    target = ROOT / relative
    if target.exists():
        assert target.read_bytes() == original.read_bytes(), relative
    records.append((relative, original, original_object, target))

# Validate every source and object before changing the receiving project.
cache_path = ROOT / 'verification/build_cache.json'
cache = json.loads(cache_path.read_text(encoding='utf-8'))
added = 0
for relative, original, original_object, target in records:
    if not target.exists():
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(original, target)
        output = ROOT / '.lake/build/lib/lean' / relative.with_suffix('.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(original_object, output)
        cache['sourceSha256'][str(relative)] = digest(target)
        cache['objectSha256'][str(relative)] = digest(output)
        added += 1
cache['completedAxiomAudit'] = False
cache_path.write_text(json.dumps(cache, indent=2), encoding='utf-8')
provenance = ROOT / 'third-party/SectionTwo'
provenance.mkdir(parents=True, exist_ok=True)
for name in ['manifest.json', 'axioms.log', 'status.txt']:
    shutil.copyfile(SOURCE / 'verification' / name, provenance / name)
for name in ['README.md', 'COVERAGE.md']:
    shutil.copyfile(SOURCE / name, provenance / name)
result = {
    'capturedUtc': datetime.now(timezone.utc).isoformat(),
    'sourceProject': str(SOURCE),
    'sourcePaperCommit': manifest['sourceCommit'],
    'sourceAuditCompletedUtc': manifest['completedUtc'],
    'sourceAuditedDeclarations': manifest['auditedDeclarations'],
    'scope': 'Completed Section 2 and required Appendix A; exact audited 357-module snapshot.',
    'objects': '24 earlier modules were rebuilt locally; newly added objects are source/hash-verified reuse from the completed Section 2 audit, not rebuilt this round.',
    'sourceSha256': {str(relative): digest(target) for relative, _, _, target in records},
    'importedObjectSha256': {str(relative): digest(original_object) for relative, _, original_object, _ in records},
}
(ROOT / 'SECTION2_COMPLETED_SOURCE_MANIFEST.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
root = ROOT / 'IGSIII34.lean'
imports = root.read_text(encoding='utf-8')
if 'import IGSIII.SectionTwo\n' not in imports:
    root.write_text(imports + 'import IGSIII.SectionTwo\n', encoding='utf-8', newline='\n')
print(json.dumps({'verifiedSnapshotModules': len(records), 'newModules': added, 'liveProjectModified': False}))
