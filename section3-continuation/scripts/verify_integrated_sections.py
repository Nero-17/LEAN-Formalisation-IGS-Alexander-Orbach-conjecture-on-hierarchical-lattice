"""Compile the integrated Sections3–4 closure and audit its actual interfaces and transitive axioms."""
from pathlib import Path
import hashlib
import json
import re
import os
import subprocess
import sys
import time
from lean_slots import compiler_slot
from datetime import datetime, timezone

sys.stdout.reconfigure(encoding='utf-8')

ROOT = Path(__file__).resolve().parents[1]
LAKE = str(Path.home() / '.elan/bin/lake.exe') if sys.platform == 'win32' else 'lake'
VERIFY = ROOT / 'verification' / 'section34'
VERIFY.mkdir(exist_ok=True)
STATUS = VERIFY / 'status.txt'
FROZEN_PAPER_SHA256 = '207204ef8eaffc8240324349e3b94929ede9a7a129b0e1d63298f1ff49af5d51'


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def without_comments(source):
    result, index, depth = [], 0, 0
    while index < len(source):
        pair = source[index:index + 2]
        if pair == '/-':
            depth += 1
            result.append('  ')
            index += 2
        elif depth and pair == '-/':
            depth -= 1
            result.append('  ')
            index += 2
        elif depth:
            result.append('\n' if source[index] == '\n' else ' ')
            index += 1
        elif pair == '--':
            newline = source.find('\n', index)
            if newline < 0:
                break
            result.append('\n')
            index = newline + 1
        else:
            result.append(source[index])
            index += 1
    if depth:
        raise ValueError('Unterminated Lean block comment')
    return ''.join(result)


def declarations(source):
    scopes, result = [], []
    for line in without_comments(source).splitlines():
        namespace = re.match(r'^namespace\s+(\S+)', line)
        section = re.match(r'^(?:noncomputable\s+)?section(?:\s|$)', line)
        end = re.match(r'^end(?:\s|$)', line)
        declaration = re.match(r'^(?:@\[[^\]]+\]\s*)*(?:noncomputable\s+)?'
                               r'(?:theorem|lemma|def|abbrev|structure)\s+([^\s:(]+)', line)
        if namespace:
            scopes.append(namespace.group(1))
        elif section:
            scopes.append('')
        elif end:
            scopes.pop()
        elif declaration:
            result.append('.'.join([name for name in scopes if name] + [declaration.group(1)]))
    return result


def run(arguments, echo=True):
    environment = os.environ.copy()
    if sys.platform == 'win32':
        environment['ELAN_HOME'] = str(Path.home() / '.elan')
        environment['GIT_CONFIG_COUNT'] = '1'
        environment['GIT_CONFIG_KEY_0'] = 'safe.directory'
        environment['GIT_CONFIG_VALUE_0'] = '*'
    with compiler_slot():
        process = subprocess.run([LAKE, 'env', 'lean', *arguments], cwd=ROOT,
                                 env=environment,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                 text=True, encoding='utf-8', errors='replace')
    if echo:
        print(process.stdout, end='', flush=True)
    if process.returncode:
        raise RuntimeError(f'Lean failed: {arguments}')
    return process.stdout


def main():
    manuscript = ROOT / 'paper/main.tex'
    if manuscript.exists() and sha256(manuscript) != FROZEN_PAPER_SHA256:
        raise RuntimeError('Manuscript differs from the frozen Section 3 source')
    STATUS.write_text('Verification running; this is not a completed manuscript formalisation.\n', encoding='utf-8')
    source_paths = sorted((ROOT / 'IGSIII34').rglob('*.lean')) + sorted((ROOT / 'IGSIII').rglob('*.lean')) + sorted((ROOT / 'IGSIII4').rglob('*.lean'))
    modules = {'.'.join(path.relative_to(ROOT).with_suffix('').parts): path for path in source_paths}
    modules['IGSIII34'] = ROOT / 'IGSIII34.lean'
    modules['IGSIII'] = ROOT / 'IGSIII.lean'
    modules['IGSIII4'] = ROOT / 'IGSIII4.lean'
    modules['IGSIIISectionsThreeFour'] = ROOT / 'IGSIIISectionsThreeFour.lean'
    modules['IGSAlexanderOrbach'] = ROOT / 'IGSAlexanderOrbach.lean'
    imported_only = '--imported-only' in sys.argv
    request_section_three_complete = '--complete' in sys.argv
    if imported_only:
        imported_modules = {}
        def include(module):
            if module not in modules or module in imported_modules:
                return
            imported_modules[module] = modules[module]
            for dependency in re.findall(r'^import\s+(\S+)', modules[module].read_text(encoding='utf-8-sig'), re.M):
                include(dependency)
        include('IGSAlexanderOrbach')
        modules = imported_modules
    before = {str(path.relative_to(ROOT)): sha256(path) for path in modules.values()}
    order, visiting, visited = [], set(), set()

    def visit(module):
        if module in visited:
            return
        if module in visiting:
            raise RuntimeError(f'Cyclic import: {module}')
        visiting.add(module)
        for dependency in re.findall(r'^import\s+(\S+)', modules[module].read_text(encoding='utf-8-sig'), re.M):
            if dependency in modules:
                visit(dependency)
        visiting.remove(module)
        visited.add(module)
        order.append(module)

    for module in modules:
        visit(module)
    previous_path = VERIFY / 'manifest.json'
    cache_path = VERIFY / 'build_cache.json'
    previous = json.loads((cache_path if cache_path.exists() else previous_path).read_text(encoding='utf-8')) if (cache_path.exists() or previous_path.exists()) else {}
    previous_sources = previous.get('sourceSha256', {})
    previous_objects = previous.get('objectSha256', {})
    log, names, objects = [], [], {}
    for module in order:
        path = modules[module]
        source = path.read_text(encoding='utf-8-sig')
        if re.search(r'\b(?:sorry|admit|sorryAx)\b|^\s*(?:axiom|opaque)\b', without_comments(source), re.M):
            raise RuntimeError(f'Proof hole or new axiom in {path}')
        relative = path.relative_to(ROOT)
        output = ROOT / '.lake/build/lib/lean' / relative.with_suffix('.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        unchanged = (previous_sources.get(str(relative)) == before[str(relative)] and
                     output.exists() and previous_objects.get(str(relative)) == sha256(output))
        for dependency in re.findall(r'^import\s+(\S+)', source, re.M):
            if dependency in modules:
                dependency_relative = str(modules[dependency].relative_to(ROOT))
                if (previous_sources.get(dependency_relative) != before[dependency_relative] or
                    previous_objects.get(dependency_relative) != objects.get(dependency_relative)):
                    unchanged = False
        if unchanged:
            print(f'Verified unchanged {module}', flush=True)
            log.append(f'Verified unchanged against prior source/object hashes: {module}')
        else:
            print(f'Compiling {module}', flush=True)
            log.append(f'Compiling {module}\n' + run(['-o', str(output), str(relative)]))
        objects[str(relative)] = sha256(output)
        # This cache records successful compilation only, never a completed axiom audit.
        if sha256(path) != before[str(relative)]:
            raise RuntimeError(f'Source changed during compilation: {relative}')
        cached_sources = dict(previous_sources)
        cached_objects = dict(previous_objects)
        cached_sources.update({str(modules[done].relative_to(ROOT)): before[str(modules[done].relative_to(ROOT))]
                               for done in order[:order.index(module) + 1]})
        cached_objects.update(objects)
        pending_cache = cache_path.with_suffix(f'.{os.getpid()}.json.tmp')
        pending_cache.write_text(json.dumps({
            'sourceSha256': cached_sources,
            'objectSha256': cached_objects,
            'completedAxiomAudit': False,
        }, indent=2), encoding='utf-8')
        # Windows indexers/readers may briefly hold a file without delete sharing.
        # Preserve the previous cache and retry the atomic replacement; never
        # treat a failed write as a completed build or axiom certificate.
        for attempt in range(21):
            try:
                os.replace(pending_cache, cache_path)
                break
            except PermissionError:
                if attempt == 20:
                    raise
                time.sleep(0.1)
        names.extend(declarations(source))
    (VERIFY / 'build.log').write_text('\n'.join(log), encoding='utf-8')
    audit = ROOT / 'Section34AxiomAudit.lean'
    audit.write_text('''import IGSAlexanderOrbach
import Lean
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let environment ← getEnv
  let mut audited : Nat := 0
  for moduleName in environment.allImportedModuleNames do
    if (`IGSIII34).isPrefixOf moduleName || (`IGSIII).isPrefixOf moduleName || (`IGSIII4).isPrefixOf moduleName || moduleName == `IGSIIISectionsThreeFour || moduleName == `IGSAlexanderOrbach then
      logInfo m!"IMPORTED {moduleName}"
  for (declaration, _) in environment.constants do
    if let some moduleIndex := environment.getModuleIdxFor? declaration then
      let moduleName := environment.allImportedModuleNames[moduleIndex.toNat]!
      if (`IGSIII34).isPrefixOf moduleName || (`IGSIII).isPrefixOf moduleName || (`IGSIII4).isPrefixOf moduleName || moduleName == `IGSIIISectionsThreeFour || moduleName == `IGSAlexanderOrbach then
        let axioms ← collectAxioms declaration
        for axiomName in axioms do
          unless axiomName == `propext || axiomName == `Classical.choice || axiomName == `Quot.sound do
            throwError "Unexpected axiom {axiomName} in {declaration}"
        logInfo m!"AUDITED {moduleName} {declaration}: {axioms}"
        audited := audited + 1
  if audited == 0 then throwError "No project declarations audited"
  for target in #[`IGSIII4.section_four_for_natural_resistance,
      `IGSIII4.exists_section_four_from_proved_sections_two_three,
      `IGSIII4.natural_critical_supersolution,
      `IGSIII4.natural_long_diamond_spectral_dimension_strictly_below_four_thirds,
      `IGSIII4.exists_ae_actual_section_four_typical_heat_kernel,
      `IGSIII4.exists_actual_section_four_and_typical_heat_kernel] do
    let some information := environment.find? target | throwError "Missing actual interface {target}"
    let mut type := information.type
    let mut parameters : Nat := 0
    let mut scanning := true
    while scanning do
      match type with
      | .forallE binder domain body _ =>
        if #[`accepted, `upper, `pruning, `acceptedSectionThreeFormula].contains binder then
          throwError "Former assumed input {binder} remains in {target}"
        if let .const domainName _ := domain.getAppFn then
          if #[`IGSIII4.AcceptedElectricalSectionThree,
              `IGSIII4.AcceptedResistanceMeanUpperSectionThree,
              `IGSIII4.AcceptedCorePruningSectionThree].contains domainName then
            throwError "Former assumed certificate {domainName} remains in {target}"
        type := body
        parameters := parameters + 1
      | _ => scanning := false
    if target == `IGSIII4.exists_section_four_from_proved_sections_two_three ||
        target == `IGSIII4.exists_actual_section_four_and_typical_heat_kernel then
      unless parameters == 6 do
        throwError "The final model-only theorem {target} has {parameters} inputs, expected six"
    logInfo m!"ACTUAL_INTERFACE {target} PARAMETERS {parameters}"
  logInfo m!"AUDIT_TOTAL {audited}"
''', encoding='utf-8')
    output = run(['Section34AxiomAudit.lean'], echo=False)
    (VERIFY / 'axioms.log').write_text(output, encoding='utf-8')
    audited = re.findall(r'AUDITED (\S+) (\S+): (.*)', output)
    totals = re.findall(r'AUDIT_TOTAL (\d+)', output)
    if len(totals) != 1 or int(totals[0]) != len(audited):
        raise RuntimeError('Incomplete module-origin axiom audit')
    names = [declaration for module, declaration, axioms in audited]
    imported_names = set(re.findall(r'IMPORTED (\S+)', output))
    if set(modules) - imported_names:
        raise RuntimeError(f'Compiled project modules absent from axiom audit: {set(modules) - imported_names}')
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    # Lean itself rejects every unexpected transitive axiom. The module-origin
    # enumeration includes private declarations and generated recursors/equations.
    current_paths = list(modules.values()) if imported_only else source_paths + [ROOT / 'IGSIII34.lean', ROOT / 'IGSIII.lean']
    after = {str(path.relative_to(ROOT)): sha256(path) for path in current_paths}
    if before != after:
        raise RuntimeError('Sources changed during verification')
    correspondence = None
    if request_section_three_complete:
        correspondence_path = ROOT / 'verification/section3_correspondence.json'
        if not correspondence_path.exists():
            raise RuntimeError('Completion requires the reviewed manuscript-obligation correspondence')
        correspondence = json.loads(correspondence_path.read_text(encoding='utf-8-sig'))
        if (correspondence.get('status') != 'complete' or
                correspondence.get('sourcePaperSha256') != FROZEN_PAPER_SHA256 or
                correspondence.get('unresolvedObligations')):
            raise RuntimeError('Manuscript correspondence is incomplete or belongs to another source')
        obligations = correspondence.get('obligations', [])
        if not obligations:
            raise RuntimeError('No manuscript obligations were reviewed')
        portable_source_hashes = {name.replace('\\', '/'): digest for name, digest in after.items()}
        for obligation in obligations:
            if not obligation.get('reviewed') or not obligation.get('entryPoints'):
                raise RuntimeError('Unreviewed obligation: ' + obligation.get('label', '<unnamed>'))
            for entry in obligation['entryPoints']:
                if entry['declaration'] not in names:
                    raise RuntimeError('Obligation theorem absent from audited closure: ' + entry['declaration'])
                if portable_source_hashes.get(entry['source'].replace('\\', '/')) != entry['sha256']:
                    raise RuntimeError('Obligation source changed: ' + entry['source'])
    section_four_correspondence = None
    if request_section_three_complete:
        section_four_path = VERIFY / 'section4_correspondence.json'
        section_four_correspondence = json.loads(section_four_path.read_text(encoding='utf-8'))
        if (section_four_correspondence.get('status') != 'complete' or
                section_four_correspondence.get('sourcePaperSha256') != FROZEN_PAPER_SHA256 or
                section_four_correspondence.get('unresolvedObligations')):
            raise RuntimeError('Section4 manuscript/interface correspondence is incomplete')
        if not section_four_correspondence.get('obligations'):
            raise RuntimeError('No Section4 obligations reviewed')
        for obligation in section_four_correspondence['obligations']:
            if not obligation.get('reviewed') or not obligation.get('entryPoints'):
                raise RuntimeError('Unreviewed Section4 obligation: ' + obligation.get('label', '<unnamed>'))
            for entry in obligation['entryPoints']:
                if entry['declaration'] not in names:
                    raise RuntimeError('Section4 theorem absent from audited closure: ' + entry['declaration'])
                if portable_source_hashes.get(entry['source'].replace('\\', '/')) != entry['sha256']:
                    raise RuntimeError('Section4 obligation source changed: ' + entry['source'])
        actual_interfaces = re.findall(r'ACTUAL_INTERFACE (\S+) PARAMETERS (\d+)', output)
        if len(actual_interfaces) != 6:
            raise RuntimeError('Final actual interfaces were not all audited')
    manifest = {
        'verifiedUtc': datetime.now(timezone.utc).isoformat(),
        'sourcePaperCommit': 'db2cbd8163ef90cc70ebd4d97f282993fd3311b6',
        'sourcePaperSha256': FROZEN_PAPER_SHA256,
        'sourcePaperLocallyAvailable': manuscript.exists(),
        'leanToolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'mathlibRevision': '520045ab14e26149ee970e2e617ca04b09bde5d6',
        'auditedDeclarations': names,
        'auditEnumeration': 'all environment declarations owned by imported IGSIII/IGSIII34/IGSIII4 modules',
        'auditedDeclarationCount': len(names),
        'auditedModules': sorted({module for module, declaration, axioms in audited}),
        'importedProjectModules': sorted(imported_names),
        'auditScope': 'aggregate import closure; unimported work in progress excluded' if imported_only else 'all local project source modules',
        'allowedAxioms': sorted(allowed),
        'sourceSha256': after,
        'objectSha256': objects,
        'buildConfigurationSha256': {name: sha256(ROOT / name)
            for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']},
        'manuscriptFormalisationComplete': request_section_three_complete,
        'integratedSectionFourComplete': request_section_three_complete,
        'aggregateRoot': 'IGSAlexanderOrbach',
        'remainingAssumedSectionThreeResultsInActualEntrypoints': [],
        'globalAlexanderOrbachExclusion': 'conjecture only; not proved',
        'actualInterfaceAudit': re.findall(r'ACTUAL_INTERFACE (\S+) PARAMETERS (\d+)', output),
        'section4CorrespondenceSha256': sha256(VERIFY / 'section4_correspondence.json')
            if section_four_correspondence is not None else None,
        'section3CorrespondenceSha256': sha256(ROOT / 'verification/section3_correspondence.json')
            if correspondence is not None else None,
    }
    (VERIFY / 'manifest.json').write_text(json.dumps(manifest, indent=2, ensure_ascii=False), encoding='utf-8')
    manuscript_status = ('Sections3–4 manuscript correspondence, actual-interface and aggregate audit complete. See the exact scope in SECTION34_COVERAGE.md.\n'
                         if request_section_three_complete else
                         'Integrated preliminary audit only; final correspondence review pending. The completed Section3 certificate is preserved. See COVERAGE.md.\n')
    STATUS.write_text(f'Build and axiom audit passed for {len(names)} declarations.\n' + manuscript_status,
                      encoding='utf-8')
    print(STATUS.read_text(), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        STATUS.write_text(f'Verification incomplete: {error}\n', encoding='utf-8')
        raise
