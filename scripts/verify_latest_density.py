"""Independently verify one frozen aggregate's complete local import closure.

Run from any checkout with --root CHECKOUT --output NEW_REPORT_DIRECTORY.
Compilation caches are evidence about bytes only, never semantic certificates.
All local module-owned constants, including private/generated constants, receive
a fresh transitive axiom audit. Manuscript correspondence needs separate review.
"""
from __future__ import annotations

import argparse
from contextlib import nullcontext
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def write_json(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


def without_comments(source: str) -> str:
    result, depth, index = [], 0, 0
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


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--aggregate', default='IGSAlexanderOrbach')
    parser.add_argument('--seed-manifest', type=Path, action='append', default=[])
    parser.add_argument('--required-module', action='append', default=[])
    parser.add_argument('--fresh-module', action='append', default=[])
    parser.add_argument('--interface', action='append', default=[])
    parser.add_argument('--manuscript', type=Path)
    parser.add_argument('--manuscript-sha256')
    parser.add_argument('--source-commit')
    parser.add_argument('--inspect-only', action='store_true')
    parser.add_argument('--compile-only', action='store_true')
    arguments = parser.parse_args()
    root = arguments.root.resolve()
    output = arguments.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    started = utc()
    status = output / 'status.txt'
    status.write_text('Verification incomplete; no completion certificate.\n', encoding='utf-8')
    script_hash = digest(Path(__file__))
    environment = os.environ.copy()
    if sys.platform == 'win32':
        environment['ELAN_HOME'] = str(Path.home() / '.elan')
        environment.update(GIT_CONFIG_COUNT='1', GIT_CONFIG_KEY_0='safe.directory', GIT_CONFIG_VALUE_0='*')
    lake = str(Path.home() / '.elan/bin/lake.exe') if sys.platform == 'win32' else (shutil.which('lake') or 'lake')
    slot = nullcontext
    if (root / 'scripts/lean_slots.py').exists():
        sys.path.insert(0, str(root / 'scripts'))
        from lean_slots import compiler_slot
        slot = compiler_slot
    configuration = {name: digest(root / name) for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']}
    for name in ['vendor/Universality/lean-toolchain', 'vendor/Universality/lakefile.toml', 'vendor/Universality/lake-manifest.json']:
        if (root / name).exists():
            configuration[name] = digest(root / name)
    # The vendored Universality source is part of the audited local closure.
    local_roots = [root]
    if (root / 'vendor/Universality').is_dir():
        local_roots.append(root / 'vendor/Universality')
    modules, external, visiting, order = {}, set(), set(), []

    def include(module: str) -> None:
        if module in visiting:
            raise RuntimeError('Import cycle: ' + module)
        if module in modules:
            return
        relative = Path(*module.split('.')).with_suffix('.lean')
        # Lake resolves this required package through vendor/Universality.
        # A public checkout may also retain unrelated legacy root sources.
        candidates = list(reversed(local_roots)) if module == 'Universality' or module.startswith('Universality.') else local_roots
        owner = next((location for location in candidates if (location / relative).exists()), None)
        if owner is None:
            external.add(module)
            return
        path = owner / relative
        cleaned = without_comments(path.read_text(encoding='utf-8-sig'))
        if re.search(r'\b(?:sorry|admit|sorryAx)\b|^\s*(?:axiom|opaque)\b', cleaned, re.M):
            raise RuntimeError('Proof hole or declared axiom in ' + str(path))
        imports = re.findall(r'^\s*import\s+(\S+)', cleaned, re.M)
        modules[module] = {'source': path.relative_to(root).as_posix(),
                           'owner': owner.relative_to(root).as_posix(),
                           'sourceSha256': digest(path), 'imports': imports,
                           'object': (owner / '.lake/build/lib/lean' / relative.with_suffix('.olean')).relative_to(root).as_posix()}
        visiting.add(module)
        for dependency in imports:
            include(dependency)
        visiting.remove(module)
        order.append(module)

    include(arguments.aggregate)
    if arguments.aggregate not in modules:
        raise RuntimeError('Aggregate is not a local module')
    absent = set(arguments.required_module) - set(modules)
    if absent:
        raise RuntimeError('Required modules absent from closure: ' + ', '.join(sorted(absent)))
    if arguments.manuscript_sha256 and not arguments.manuscript:
        raise RuntimeError('Expected manuscript hash requires manuscript file')
    manuscript_hash = digest(arguments.manuscript) if arguments.manuscript else None
    if arguments.manuscript_sha256 and manuscript_hash != arguments.manuscript_sha256:
        raise RuntimeError('Frozen manuscript hash mismatch')
    write_json(output / 'closure_inputs.json', {'startedUtc': started, 'aggregate': arguments.aggregate,
        'moduleCount': len(modules), 'modules': modules, 'externalDirectImports': sorted(external),
        'buildConfigurationSha256': configuration, 'sourcePaperSha256': manuscript_hash})
    print(f'Closure: {len(modules)} local modules; {len(external)} external direct imports', flush=True)
    if arguments.inspect_only:
        print('Inspection only; no compilation or acceptance asserted.', flush=True)
        return

    seed_paths = list(arguments.seed_manifest)
    cache_path = output / 'build_cache.json'
    if cache_path.exists():
        seed_paths.append(cache_path)
    seeds = []
    for seed_path in seed_paths:
        value = json.loads(seed_path.read_text(encoding='utf-8-sig'))
        seed_configuration = value.get('buildConfigurationSha256', {})
        if any(seed_configuration.get(name) != configuration[name] for name in ['lean-toolchain', 'lake-manifest.json']):
            print('Skipping seed with no matching toolchain/dependency-lock fingerprint: ' + str(seed_path), flush=True)
            continue
        sources = {key.replace('\\', '/'): val for key, val in value.get('sourceSha256', {}).items()}
        objects = {key.replace('\\', '/'): val for key, val in value.get('objectSha256', {}).items()}
        seeds.append({'path': str(seed_path), 'sha256': digest(seed_path), 'sources': sources, 'objects': objects,
                      'dependencyObjectSha256': value.get('dependencyObjectSha256', {})})
    compiled, reused, objects, dependency_objects, receipts = [], [], {}, {}, []

    def save_cache() -> None:
        write_json(cache_path, {'sourceSha256': {modules[name]['source']: modules[name]['sourceSha256'] for name in order if modules[name]['source'] in objects},
            'objectSha256': objects, 'dependencyObjectSha256': dependency_objects,
            'buildConfigurationSha256': configuration,
            'completedAxiomAudit': False, 'aggregate': arguments.aggregate, 'updatedUtc': utc()})

    for index, module in enumerate(order):
        entry = modules[module]
        relative = entry['source']
        source = root / relative
        object_path = root / entry['object']
        local_dependencies = {modules[dependency]['source']: objects[modules[dependency]['source']]
                              for dependency in entry['imports'] if dependency in modules}
        candidate = None
        if module not in arguments.fresh_module and object_path.exists():
            object_hash = digest(object_path)
            for seed in reversed(seeds):
                if seed['sources'].get(relative) != entry['sourceSha256'] or seed['objects'].get(relative) != object_hash:
                    continue
                known_dependencies = seed['dependencyObjectSha256'].get(relative)
                if known_dependencies is None:
                    # A historical full-closure snapshot is usable only when all
                    # its recorded direct imported objects still match.
                    known_dependencies = {dependency: seed['objects'].get(dependency) for dependency in local_dependencies}
                if known_dependencies == local_dependencies:
                    candidate = seed
                    break
        compile_started = utc()
        if candidate is None:
            object_path.parent.mkdir(parents=True, exist_ok=True)
            print(f'[{index + 1}/{len(order)}] Compiling {module}', flush=True)
            with slot():
                result = subprocess.run([lake, 'env', 'lean', '--root=' + str(root / entry['owner']), '-o', str(object_path), str(source)],
                    cwd=root, env=environment, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    text=True, encoding='utf-8', errors='replace')
            log_path = output / (module.replace('.', '__') + '.compile.log')
            log_path.write_text(result.stdout, encoding='utf-8')
            receipt = {'module': module, 'source': relative, 'sourceSha256': entry['sourceSha256'],
                'sourceUnchanged': digest(source) == entry['sourceSha256'], 'returnCode': result.returncode,
                'objectSha256': digest(object_path) if result.returncode == 0 and object_path.exists() else None,
                'directLocalDependencyObjectSha256': local_dependencies,
                'startedUtc': compile_started, 'endedUtc': utc(), 'logSha256': digest(log_path)}
            write_json(output / (module.replace('.', '__') + '.compile.json'), receipt)
            receipts.append(receipt)
            if result.returncode or not receipt['sourceUnchanged']:
                save_cache()
                print(result.stdout, flush=True)
                raise RuntimeError('Fresh compilation failed: ' + module)
            compiled.append(module)
        else:
            reused.append({'module': module, 'seedPath': candidate['path'], 'seedSha256': candidate['sha256']})
        if digest(source) != entry['sourceSha256']:
            raise RuntimeError('Source changed during compilation: ' + relative)
        objects[relative] = digest(object_path)
        dependency_objects[relative] = local_dependencies
        if candidate is None or index % 100 == 0:
            save_cache()
    save_cache()
    if arguments.compile_only:
        print(f'Compilation-only checkpoint: {len(compiled)} fresh, {len(reused)} exact cache matches. No final certificate.', flush=True)
        return

    module_names = ',\n    '.join('`' + module for module in sorted(modules))
    interface_names = ',\n    '.join('`' + interface for interface in arguments.interface)
    probe = f'''import {arguments.aggregate}
import Lean
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let environment ← getEnv
  let selected : Array Name := #[{module_names}]
  let mut audited : Nat := 0
  for moduleName in environment.allImportedModuleNames do
    if selected.contains moduleName then
      logInfo m!"IMPORTED {{moduleName}}"
  for (declaration, _) in environment.constants do
    if let some moduleIndex := environment.getModuleIdxFor? declaration then
      let moduleName := environment.allImportedModuleNames[moduleIndex.toNat]!
      if selected.contains moduleName then
        let axioms ← collectAxioms declaration
        for axiomName in axioms do
          unless axiomName == `propext || axiomName == `Classical.choice || axiomName == `Quot.sound do
            throwError "Unexpected axiom {{axiomName}} in {{declaration}}"
        logInfo m!"AUDITED {{moduleName}} {{declaration}}: {{axioms}}"
        audited := audited + 1
  if audited == 0 then throwError "No local declarations audited"
  let interfaces : Array Name := #[{interface_names}]
  for target in interfaces do
    let some information := environment.find? target | throwError "Missing required interface {{target}}"
    logInfo m!"INTERFACE {{target}}: {{information.type}}"
  logInfo m!"AUDIT_TOTAL {{audited}}"
'''
    probe_path = output / 'closure_axiom_probe.lean.txt'
    probe_path.write_text(probe, encoding='utf-8')
    print('Fresh full module-origin transitive axiom audit', flush=True)
    with slot():
        result = subprocess.run([lake, 'env', 'lean', '--stdin'], input=probe, cwd=root, env=environment,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, encoding='utf-8', errors='replace')
    axiom_log = output / 'closure_axioms.log'
    axiom_log.write_text(result.stdout, encoding='utf-8')
    audited = re.findall(r'AUDITED (\S+) (\S+): (.*)', result.stdout)
    imported = set(re.findall(r'IMPORTED (\S+)', result.stdout))
    totals = re.findall(r'AUDIT_TOTAL (\d+)', result.stdout)
    if result.returncode or len(totals) != 1 or int(totals[0]) != len(audited) or imported != set(modules):
        print(result.stdout[-12000:], flush=True)
        raise RuntimeError('Incomplete or failed axiom audit')
    if len({name for _, name, _ in audited}) != len(audited):
        raise RuntimeError('Repeated declarations in audit log')
    for module, entry in modules.items():
        if digest(root / entry['source']) != entry['sourceSha256'] or digest(root / entry['object']) != objects[entry['source']]:
            raise RuntimeError('Source/object changed during final audit: ' + module)
    if configuration != {name: digest(root / name) for name in configuration}:
        raise RuntimeError('Build configuration changed during audit')
    if arguments.manuscript and digest(arguments.manuscript) != manuscript_hash:
        raise RuntimeError('Manuscript changed during audit')
    if digest(Path(__file__)) != script_hash:
        raise RuntimeError('Verifier changed during audit')
    manifest = {'passed': True, 'disposition': 'ACCEPT KERNEL, HASH AND AXIOM GATE ONLY',
        'semanticCorrespondenceRequiresSeparateReview': True, 'latestManuscriptComplete': False,
        'startedUtc': started, 'endedUtc': utc(), 'aggregate': arguments.aggregate,
        'leanToolchain': (root / 'lean-toolchain').read_text().strip(),
        'sourcePaperSha256': manuscript_hash, 'sourcePaperCommit': arguments.source_commit,
        'buildConfigurationSha256': configuration,
        'sourceSha256': {entry['source']: entry['sourceSha256'] for entry in modules.values()},
        'objectSha256': objects, 'dependencyObjectSha256': dependency_objects,
        'moduleCount': len(modules), 'importedLocalModules': sorted(imported),
        'externalDirectImports': sorted(external), 'freshCompiledModules': compiled,
        'cacheReusedModules': reused, 'auditedDeclarationCount': len(audited),
        'auditedDeclarations': [name for _, name, _ in audited],
        'auditEnumeration': 'All constants owned by every imported local module, including vendored Universality, private and generated constants',
        'allowedAxioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'requiredInterfaces': arguments.interface, 'requiredModules': arguments.required_module,
        'probeSha256': digest(probe_path), 'axiomLogSha256': digest(axiom_log), 'verifierSha256': script_hash,
        'sourceObjectsConfigurationUnchanged': True}
    write_json(output / 'closure_manifest.json', manifest)
    status.write_text(f'PASS: {len(modules)} local modules; {len(audited)} declarations.\nKernel/hash/axiom gate only; semantic review is separate.\n', encoding='utf-8')
    print(status.read_text(), flush=True)


if __name__ == '__main__':
    if hasattr(sys.stdout, 'reconfigure'):
        sys.stdout.reconfigure(encoding='utf-8')
    main()
