"""Import the pinned MIT-licensed complete finite-dimensional fixed-point proof.

This is a source import, not a copied compiled certificate. Only imports and
the enclosing namespace are adapted here. Further compatibility edits, if any,
must be recorded separately and are checked by the project verifier.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
SOURCE = Path('C:/Users/lzysh/Documents/Codex/2026-09-07/new-chat/work/'
              'section4-round5-topology-sources/harfe-770940d')
COMMIT = '770940ddf9878cf61952ed53d910b92bca841838'
FILES = {
    'cubical_sperner_prep': 'VendorSpernerPrep',
    'cubical_sperner': 'VendorSperner',
    'apply_cubical_sperner': 'VendorSpernerApplication',
    'convex_homeos': 'VendorConvexHomeomorphisms',
    'brouwer': 'VendorBrouwer',
}
TACTICS = ['ByContra', 'Cases', 'Choose', 'Contrapose', 'Convert', 'FieldSimp', 'FinCases',
           'FunProp', 'GCongr', 'IntervalCases', 'Linarith', 'NormNum',
           'Positivity', 'Push', 'Ring', 'Set', 'Tauto']
DESTINATION = ROOT / 'IGSIII34/Topology'
DESTINATION.mkdir(parents=True, exist_ok=True)
NOTICE = ROOT / 'third-party'
NOTICE.mkdir(exist_ok=True)
(NOTICE / 'Harfe-MIT.txt').write_bytes((SOURCE / 'LICENSE').read_bytes())
entries = []
for original, renamed in FILES.items():
    original_path = SOURCE / f'FixedPointTheorems/{original}.lean'
    original_bytes = original_path.read_bytes()
    text = original_bytes.decode('utf-8-sig')
    for old_import, new_import in FILES.items():
        text = text.replace(f'import FixedPointTheorems.{old_import}',
                            f'import IGSIII34.Topology.{new_import}')
    text = text.replace('import Mathlib.Tactic\n',
                        ''.join(f'import Mathlib.Tactic.{name}\n' for name in TACTICS))
    last_import = list(re.finditer(r'^import[^\n]*\n', text, re.M))[-1].end()
    text = text[:last_import] + '\nnamespace IGSIII34.Topology.Vendor\n' + text[last_import:]
    text += '\nend IGSIII34.Topology.Vendor\n'
    header = (f'/-\nCopyright (c) 2026 harfe. MIT license: third-party/Harfe-MIT.txt.\n'
              f'Upstream: https://github.com/harfe/fixed-point-theorems-lean4/tree/{COMMIT}\n'
              f'Original file: FixedPointTheorems/{original}.lean\n'
              'Local adaptation: imports and enclosing namespace only.\n-/\n')
    destination = DESTINATION / f'{renamed}.lean'
    if destination.exists():
        raise RuntimeError(f'Refusing to overwrite {destination}')
    destination.write_text(header + text, encoding='utf-8')
    entries.append({'sourceFile': str(original_path),
                    'originalSha256': hashlib.sha256(original_bytes).hexdigest(),
                    'localFile': str(destination.relative_to(ROOT)),
                    'importedSha256': hashlib.sha256(destination.read_bytes()).hexdigest()})
(NOTICE / 'Brouwer-source-manifest.json').write_text(json.dumps({
    'commit': COMMIT, 'license': 'MIT', 'files': entries,
    'upstreamLean': (SOURCE / 'lean-toolchain').read_text().strip(),
    'locallyRecompiled': False,
    'purpose': 'Finite-dimensional foundation only; probability-law Schauder remains unproved.'
}, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print(json.dumps({'copied': len(entries), 'commit': COMMIT}))
