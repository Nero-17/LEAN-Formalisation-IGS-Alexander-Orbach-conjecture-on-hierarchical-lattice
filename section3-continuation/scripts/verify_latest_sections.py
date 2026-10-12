"""Compile the original Sections2–4 topics (now Sections2–5) and audit actual interfaces and transitive axioms."""
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
import argparse

sys.stdout.reconfigure(encoding='utf-8')

ROOT = Path(__file__).resolve().parents[1]
LAKE = str(Path.home() / '.elan/bin/lake.exe') if sys.platform == 'win32' else 'lake'
VERIFY = ROOT / 'verification' / 'section234'
VERIFY.mkdir(exist_ok=True)
STATUS = VERIFY / 'status.txt'
FROZEN_PAPER_SHA256 = '84a8d1625fe80b5472f0ecd8938ffdcfbfb8bc62c3dff27f8e091bf473f8dc2e'
FROZEN_PAPER_COMMIT = '72298e5c47d6f5451dd8ed2e91d0b82dcd3777a3'
LATEST_AGGREGATE = 'IGSIIISectionsTwoThreeFour'
POSITIVE_INTERFACE = 'IGSIII34.Spectral.actualSpectralData_positive_laplace_variational_completion20261011'
SECTION_TWO_INTERFACE = 'IGSIII.Geometry.exists_actual_critical_section_two_geometry'
INTRINSIC_INTERFACE = 'IGSIII34.Diffusion.exists_actual_intrinsic_component_diameter_envelopes20261011'
PREFIX_VARIANCE_INTERFACE = 'IGSIII.Chemical.Substitution.exists_actual_raw_prefix_conditional_variance_rate20261011'
REQUIRED_LATEST_IMPORTS = {
    LATEST_AGGREGATE,
    'IGSIII.LatestSectionTwoSemanticAudit20261011',
    'IGSIII34.Spectral.ActualPositiveParameterResolvent20261011',
    'IGSIII34.Spectral.PositiveResolventNonzeroSupremum20261011',
    'IGSIII34.Diffusion.ActualIntrinsicResistanceDiameter20261011',
    'IGSIII34.Spectral.ActualIntrinsicComponentResolvent20261011',
    'IGSIII.Chemical.SubstitutionPaths.AllConfigurationBounds20261011',
    'IGSIII.Geometry.ExpectedChemicalMassDimension20261011',
    'IGSIII.ActualChemicalCellRouteCompletion20261011',
    'IGSIII.Chemical.SubstitutionPaths.ActualPrefixVarianceRate20261011',
    'IGSIII.Chemical.SubstitutionPaths.PrefixDepthMonotonicity20261011',
    'IGSIII.Mass.RetainedStateDefinitions20261011',
}


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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--imported-only', action='store_true',
                        help='Audit the exact aggregate import closure (always enabled).')
    parser.add_argument('--complete', action='store_true',
                        help='Require reviewed latest-source correspondence before asserting completion.')
    options = parser.parse_args()
    manuscript = ROOT / 'paper/latest-main.tex'
    if manuscript.exists() and sha256(manuscript) != FROZEN_PAPER_SHA256:
        raise RuntimeError('Private latest manuscript differs from the frozen latest Sections2–4 source')
    STATUS.write_text('Verification running; this is not a completed manuscript formalisation.\n', encoding='utf-8')
    source_paths = sorted((ROOT / 'IGSIII34').rglob('*.lean')) + sorted((ROOT / 'IGSIII').rglob('*.lean')) + sorted((ROOT / 'IGSIII4').rglob('*.lean'))
    modules = {'.'.join(path.relative_to(ROOT).with_suffix('').parts): path for path in source_paths}
    modules['IGSIII34'] = ROOT / 'IGSIII34.lean'
    modules['IGSIII'] = ROOT / 'IGSIII.lean'
    modules['IGSIII4'] = ROOT / 'IGSIII4.lean'
    modules['IGSIIISectionsThreeFour'] = ROOT / 'IGSIIISectionsThreeFour.lean'
    modules[LATEST_AGGREGATE] = ROOT / (LATEST_AGGREGATE + '.lean')
    modules['IGSAlexanderOrbach'] = ROOT / 'IGSAlexanderOrbach.lean'
    imported_only = True
    request_latest_complete = options.complete
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
    if REQUIRED_LATEST_IMPORTS - set(modules):
        raise RuntimeError('Latest aggregate is missing required imports: ' +
                           ', '.join(sorted(REQUIRED_LATEST_IMPORTS - set(modules))))
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
    # Historical certificates seed compilation hashes only. Their completion
    # flags and manuscript correspondences never satisfy the fresh gate.
    seed_directory = ROOT / 'verification/section34'
    seed_candidates = [seed_directory / 'manifest.json', seed_directory / 'build_cache.json',
                       previous_path, cache_path]
    previous_sources, previous_objects = {}, {}
    seed_provenance = []
    for candidate in seed_candidates:
        if candidate.exists():
            previous = json.loads(candidate.read_text(encoding='utf-8-sig'))
            previous_sources.update(previous.get('sourceSha256', {}))
            previous_objects.update(previous.get('objectSha256', {}))
            seed_provenance.append({'path': str(candidate.relative_to(ROOT)), 'sha256': sha256(candidate)})
    build_configuration = {name: sha256(ROOT / name)
                           for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']}
    verifier_digest = sha256(Path(__file__))
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
        if unchanged:
            # Matching source/object/dependency hashes already have a cache
            # record. Skip only its redundant rewrite; all final source/object,
            # kernel, interface and correspondence gates still run below.
            names.extend(declarations(source))
            continue
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
    audit = ROOT / 'LatestSectionsAxiomAudit.lean'
    audit.write_text('''import IGSAlexanderOrbach
import Lean
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let environment ← getEnv
  let mut audited : Nat := 0
  for moduleName in environment.allImportedModuleNames do
    if (`IGSIII34).isPrefixOf moduleName || (`IGSIII).isPrefixOf moduleName || (`IGSIII4).isPrefixOf moduleName || moduleName == `IGSIIISectionsThreeFour || moduleName == `IGSIIISectionsTwoThreeFour || moduleName == `IGSAlexanderOrbach then
      logInfo m!"IMPORTED {moduleName}"
  for (declaration, _) in environment.constants do
    if let some moduleIndex := environment.getModuleIdxFor? declaration then
      let moduleName := environment.allImportedModuleNames[moduleIndex.toNat]!
      if (`IGSIII34).isPrefixOf moduleName || (`IGSIII).isPrefixOf moduleName || (`IGSIII4).isPrefixOf moduleName || moduleName == `IGSIIISectionsThreeFour || moduleName == `IGSIIISectionsTwoThreeFour || moduleName == `IGSAlexanderOrbach then
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
      `IGSIII4.exists_actual_section_four_and_typical_heat_kernel,
      `IGSIII.Geometry.exists_actual_critical_section_two_geometry,
      `IGSIII34.Diffusion.exists_actual_intrinsic_component_diameter_envelopes20261011,
      `IGSIII34.Spectral.actualSpectralData_positive_laplace_variational_completion20261011,
      `IGSIII.Chemical.Substitution.exists_actual_raw_prefix_conditional_variance_rate20261011] do
    let some information := environment.find? target | throwError "Missing actual interface {target}"
    let mut type := information.type
    let mut parameters : Nat := 0
    let mut scanning := true
    let mut parameterPosition : Option Nat := none
    let mut positiveParameterChecked := false
    while scanning do
      match type with
      | .forallE binder domain body _ =>
        if target == `IGSIII34.Spectral.actualSpectralData_positive_laplace_variational_completion20261011 then
          if binder == `parameter then parameterPosition := some parameters
          if binder == `parameterPositive then
            let some position := parameterPosition | throwError "Positive-parameter interface has no preceding parameter binder"
            let arguments := domain.getAppArgs
            unless domain.isAppOf `LT.lt && arguments.size >= 2 do
              throwError "Positive-parameter interface does not assume strict positivity"
            let left := arguments[arguments.size - 2]!
            let right := arguments[arguments.size - 1]!
            let numeralArguments := left.getAppArgs
            unless left.isAppOf `OfNat.ofNat && numeralArguments.size >= 2 &&
                numeralArguments[1]! == .lit (.natVal 0) &&
                right == .bvar (parameters - position - 1) do
              throwError "Positive-parameter input is not exactly 0 < parameter"
            positiveParameterChecked := true
          if domain.isAppOf `LE.le then
            let arguments := domain.getAppArgs
            if let some position := parameterPosition then
              if arguments.size >= 2 && arguments[arguments.size - 1]! == .bvar (parameters - position - 1) then
                throwError "A lower-bound premise remains on the all-positive resolvent parameter"
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
        target == `IGSIII4.exists_actual_section_four_and_typical_heat_kernel ||
        target == `IGSIII34.Diffusion.exists_actual_intrinsic_component_diameter_envelopes20261011 ||
        target == `IGSIII.Geometry.exists_actual_critical_section_two_geometry ||
        target == `IGSIII.Chemical.Substitution.exists_actual_raw_prefix_conditional_variance_rate20261011 then
      unless parameters == 6 do
        throwError "The final model-only theorem {target} has {parameters} inputs, expected six"
    if target == `IGSIII34.Spectral.actualSpectralData_positive_laplace_variational_completion20261011 then
      unless positiveParameterChecked do throwError "Missing all-positive resolvent premise"
      logInfo m!"POSITIVE_PARAMETER_INTERFACE {target} EXACT_ZERO_LT_PARAMETER"
    logInfo m!"ACTUAL_INTERFACE {target} PARAMETERS {parameters}"
  logInfo m!"AUDIT_TOTAL {audited}"
''', encoding='utf-8')
    output = run(['LatestSectionsAxiomAudit.lean'], echo=False)
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
    actual_interfaces = re.findall(r'ACTUAL_INTERFACE (\S+) PARAMETERS (\d+)', output)
    if len(actual_interfaces) != 10 or len({name for name, _ in actual_interfaces}) != 10:
        raise RuntimeError('All six historical actual interfaces and four latest interfaces must be audited')
    if not {POSITIVE_INTERFACE, SECTION_TWO_INTERFACE, INTRINSIC_INTERFACE, PREFIX_VARIANCE_INTERFACE} <= {name for name, _ in actual_interfaces}:
        raise RuntimeError('Latest original-model/positive-parameter actual interfaces missing')
    if not re.search(r'POSITIVE_PARAMETER_INTERFACE \S+ EXACT_ZERO_LT_PARAMETER', output):
        raise RuntimeError('Positive-parameter signature was not certified')
    correspondence = None
    correspondence_digest = None
    correspondence_path = VERIFY / 'latest_correspondence.json'
    if request_latest_complete:
        if not correspondence_path.exists():
            raise RuntimeError('Completion requires fresh verification/section234/latest_correspondence.json')
        correspondence_digest = sha256(correspondence_path)
        correspondence = json.loads(correspondence_path.read_text(encoding='utf-8-sig'))
        if (correspondence.get('status') != 'complete' or
                correspondence.get('sourcePaperSha256') != FROZEN_PAPER_SHA256 or
                correspondence.get('sourcePaperCommit') != FROZEN_PAPER_COMMIT or
                correspondence.get('unresolvedLeanObligations') != []):
            raise RuntimeError('Latest correspondence is incomplete, has unresolved Lean obligations, or belongs to another source')
        if 'manuscriptClarifications' not in correspondence or not isinstance(correspondence['manuscriptClarifications'], list):
            raise RuntimeError('Latest correspondence must explicitly preserve manuscriptClarifications as a list')
        obligations = correspondence.get('obligations', [])
        if not obligations or not {'2', '3', '4', '5'} <= {str(item.get('section')) for item in obligations}:
            raise RuntimeError('Latest correspondence must cover Sections2,3,4,5 after the diffusion/AO split')
        labels = [item.get('label') for item in obligations]
        if any(not isinstance(label, str) or not label for label in labels) or len(labels) != len(set(labels)):
            raise RuntimeError('Latest obligation labels must be nonempty and unique')
        if manuscript.exists():
            manuscript_text = manuscript.read_text(encoding='utf-8-sig')
            latest_labels, section = set(), 0
            for line in manuscript_text.splitlines():
                if re.match(r'^\\section\*?\{', line):
                    section += 1
                if section in {2, 3, 4, 5} and re.search(r'\\begin\{(?:lemma|theorem|corollary|proposition|definition|example|aoresult|aoconjecture|conjecture)\}', line):
                    latest_labels.update(re.findall(r'\\label\{([^}]+)\}', line))
            if latest_labels - set(labels):
                raise RuntimeError('Latest labelled statements absent from correspondence: ' + ', '.join(sorted(latest_labels - set(labels))))
        portable_source_hashes = {name.replace('\\', '/'): digest for name, digest in after.items()}
        for obligation in obligations:
            if obligation.get('reviewed') is not True or not obligation.get('entryPoints'):
                raise RuntimeError('Unreviewed obligation: ' + obligation.get('label', '<unnamed>'))
            status = obligation.get('status')
            if status not in {'PROVED', 'PROVED_AFTER_SOURCE_CORRECTION', 'PROVED_WITH_EXPLICIT_POSITIVE_PARAMETER', 'OPEN_CONJECTURE'}:
                raise RuntimeError('Unsupported obligation status: ' + str(status))
            if status == 'OPEN_CONJECTURE' and obligation.get('label') != 'conj:ao-global':
                raise RuntimeError('A proved manuscript result is being left as an open conjecture')
            if obligation.get('label') == 'conj:ao-global' and status != 'OPEN_CONJECTURE':
                raise RuntimeError('The global AO conjecture must not be certified as proved')
            for entry in obligation['entryPoints']:
                if entry.get('declaration') not in names:
                    raise RuntimeError('Obligation theorem absent from audited closure: ' + str(entry.get('declaration')))
                source_name = entry.get('source', '').replace('\\', '/')
                if source_name not in portable_source_hashes or portable_source_hashes[source_name] != entry.get('sha256'):
                    raise RuntimeError('Obligation source changed or absent: ' + str(entry.get('source')))
    if build_configuration != {name: sha256(ROOT / name) for name in build_configuration} or verifier_digest != sha256(Path(__file__)):
        raise RuntimeError('Verifier or build configuration changed during verification')
    if manuscript.exists() and sha256(manuscript) != FROZEN_PAPER_SHA256:
        raise RuntimeError('Latest private manuscript changed during verification')
    if any(sha256(ROOT / '.lake/build/lib/lean' / Path(name).with_suffix('.olean')) != digest
           for name, digest in objects.items()):
        raise RuntimeError('Compiled objects changed during verification')
    if correspondence_digest is not None and sha256(correspondence_path) != correspondence_digest:
        raise RuntimeError('Reviewed latest correspondence changed during verification')
    manifest = {
        'verifiedUtc': datetime.now(timezone.utc).isoformat(),
        'sourcePaperCommit': FROZEN_PAPER_COMMIT,
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
        'buildConfigurationSha256': build_configuration,
        'verifierSha256': verifier_digest,
        'latestSectionsTwoThreeFourComplete': request_latest_complete,
        'latestSectionsTwoThroughFiveCorrectedScopeComplete': request_latest_complete,
        'sectionNumbering': 'Legacy Sections2–4 task topics now occupy Sections2–5; legacy aggregate and certificate paths are retained.',
        'certifiedScope': 'The reviewed mathematically corrected statements, with necessary source corrections explicit. The literal uncorrected manuscript is not certified.',
        'manuscriptFormalisationComplete': request_latest_complete and not correspondence['manuscriptClarifications'] if correspondence else False,
        'literalUncorrectedManuscriptComplete': request_latest_complete and not correspondence['manuscriptClarifications'] if correspondence else False,
        'manuscriptClarifications': correspondence['manuscriptClarifications'] if correspondence else [],
        'unresolvedLeanObligations': correspondence['unresolvedLeanObligations'] if correspondence else None,
        'aggregateRoot': 'IGSAlexanderOrbach',
        'remainingAssumedSectionThreeResultsInActualEntrypoints': [],
        'globalAlexanderOrbachExclusion': 'conjecture only; not proved',
        'actualInterfaceAudit': re.findall(r'ACTUAL_INTERFACE (\S+) PARAMETERS (\d+)', output),
        'latestCorrespondenceSha256': correspondence_digest,
        'historicalCompilationCacheSeeds': seed_provenance,
        'historicalCertificatesAreCompletionBasis': False,
        'privateManuscriptPath': 'paper/latest-main.tex',
    }
    (VERIFY / 'manifest.json').write_text(json.dumps(manifest, indent=2, ensure_ascii=False), encoding='utf-8')
    manuscript_status = ('Latest Sections2–5 corrected-scope correspondence, actual-interface and aggregate audit complete. Necessary manuscript corrections remain explicit in manifest.json; literal uncorrected text is not certified.\n'
                         if request_latest_complete else
                         'Latest integrated preliminary audit only; fresh correspondence review pending. Historical certificates are preserved as provenance.\n')
    STATUS.write_text(f'Build and axiom audit passed for {len(names)} declarations.\n' + manuscript_status,
                      encoding='utf-8')
    print(STATUS.read_text(), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        STATUS.write_text(f'Verification incomplete: {error}\n', encoding='utf-8')
        raise
