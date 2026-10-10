"""Record the locally recompiled external source proof without changing its sources."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
manifest_path = ROOT / 'verification/manifest.json'
manifest = json.loads(manifest_path.read_text(encoding='utf-8'))
source_manifest_path = ROOT / 'third-party/Brouwer-source-manifest.json'
source_manifest = json.loads(source_manifest_path.read_text(encoding='utf-8'))
verified_source_hashes = {path.replace('\\', '/'): digest
                         for path, digest in manifest['sourceSha256'].items()}
for entry in source_manifest['files']:
    path = ROOT / entry['localFile']
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    expected = verified_source_hashes[entry['localFile'].replace('\\', '/')]
    if digest != expected:
        raise RuntimeError(f'Source changed after audit: {path}')
    entry['verifiedLocalSha256'] = digest
source_manifest.update({
    'locallyRecompiled': True,
    'verifiedLean': (ROOT / 'lean-toolchain').read_text().strip(),
    'verifiedMathlib': '520045ab14e26149ee970e2e617ca04b09bde5d6',
    'completedAuditManifestSha256': hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
    'purpose': 'Verified finite-dimensional foundation. The project Schauder and probability-law '
               'fixed-point theorems and the positive electrical eigenlaw with all real moments are proved. '
               'Natural same-tree growth and L2/AS amplitudes are proved separately in this project. '
               'The final all-order assembly, eigenlaw uniqueness, resistance forms, diffusion '
               'and spectral limits remain incomplete.'
})
source_manifest_path.write_text(json.dumps(source_manifest, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('Recorded five locally recompiled, transitively audited external Brouwer modules.')
