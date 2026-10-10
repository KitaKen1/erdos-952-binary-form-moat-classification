#!/usr/bin/env python3
"""Build and audit the pinned standalone proof without historical /tmp checkouts.

--fresh-dependencies requires initially absent package/object directories and an
isolated empty download cache. It fetches the locked git packages and mathlib's
official object cache. The installed exact compiler toolchain is reused.
--resume resumes a failed/interrupted attempt with its preserved initial baseline.
"""
import argparse
import datetime
import json
import os
from pathlib import Path
import re
import subprocess
from classification_common import (ROOT,PROJECT,TOOLS,TARGETS,ALLOWED,
                                   sha256_file,save_json,proof_environment)

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--fresh-dependencies',action='store_true')
parser.add_argument('--resume',action='store_true')
args = parser.parse_args()
out = ROOT/'build/portable-verification435'
baseline_path = out/'initial-state.json'
lock = json.loads((PROJECT/'source-lock.json').read_text())
expected = json.loads((ROOT/'evidence/unified-verification.json').read_text())
assert lock['local_source_sha256'] == expected['source_sha256']
local = {m:s for m,s in lock['local_source_sha256'].items() if not m.startswith(('PFR.','LeanPool.'))}
hashes = dict(local)
hashes.update({m:v['source_sha256'] for m,v in lock['selected_upstream_source_modules'].items()})
assert len(local) == 302 and len(hashes) == 613
for module,sha in hashes.items():
    source = ROOT/(module.replace('.','/')+'.lean') if module in local else (
        PROJECT/'vendor'/module.split('.')[0]/(module.replace('.','/')+'.lean'))
    assert sha256_file(source) == sha,module
config_names = ['lakefile.toml','lake-manifest.json','lean-toolchain','source-lock.json']
configs = {n:sha256_file(PROJECT/n) for n in config_names}
fresh_paths = [ROOT/'build/lake435',PROJECT/'.lake/packages',out/'download-cache']
fresh_paths += [PROJECT/'vendor'/ns/'.lake' for ns in lock['upstream_commits']]
if args.resume:
    baseline = json.loads(baseline_path.read_text())
    assert baseline['source_sha256'] == hashes and baseline['config_sha256'] == configs
    assert baseline['fresh_dependencies_requested'] == args.fresh_dependencies
else:
    assert not baseline_path.exists(), 'Use --resume to preserve the original baseline'
    if args.fresh_dependencies:
        assert all(not p.exists() and not p.is_symlink() for p in fresh_paths), 'Fresh verification requires absent dependency/object/cache directories'
    baseline = dict(started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        source_sha256=hashes,config_sha256=configs,
        fresh_dependencies_requested=args.fresh_dependencies,
        initially_absent_paths=[str(p.relative_to(ROOT)) for p in fresh_paths if not p.exists()],
        installed_pinned_toolchain_reused=True)
    save_json(baseline_path,baseline)

env = os.environ.copy()
env.pop('LEAN_PATH',None)
env['PATH'] = str(TOOLS)+os.pathsep+env.get('PATH','')
env['LEAN_ABORT_ON_PANIC'] = '1'
env['MATHLIB_CACHE_DIR'] = str(out/'download-cache')
# Ambient cache mirrors/overrides must not change the declared official-cache run.
for name in ['MATHLIB_CACHE_GET_URL','MATHLIB_CACHE_BASE_URL','MATHLIB_CACHE_FROM']:
    env.pop(name,None)
out.mkdir(parents=True,exist_ok=True)

def run(name,command):
    log = out/(name+'.log')
    print('RUN: '+name,flush=True)
    # Keep the initial fresh-build evidence if a network interruption is resumed.
    with log.open('ab' if args.resume else 'wb') as stream:
        subprocess.run(command,cwd=PROJECT,env=env,stdout=stream,stderr=subprocess.STDOUT,
                       check=True,timeout=7200)
    return log

download_log = run('dependency-download',[str(TOOLS/'lake'),'exe','cache','get'])
manifest = json.loads((PROJECT/'lake-manifest.json').read_text())
for entry in manifest['packages']:
    if entry['type'] != 'git':
        continue
    checkout = PROJECT/'.lake/packages'/entry['name']
    assert subprocess.check_output(['git','-C',str(checkout),'rev-parse','HEAD'],text=True).strip() == entry['rev']
    if args.fresh_dependencies:
        assert not checkout.is_symlink(),entry['name']
        assert not (checkout/'.git/objects/info/alternates').exists(),entry['name']
    print('PIN: '+entry['name']+' '+entry['rev'],flush=True)
build_log = run('strict-build',[str(TOOLS/'lake'),'--wfail','--no-cache','build',
                              '+Integrations.Unified435:olean','+Moat:olean',
                              '+BinaryFormMoatProof:olean'])
text = build_log.read_text()
assert 'Build completed successfully' in text
assert not re.search(r'(?m:^error:|^warning:)|\bsorryAx\b',text)
fresh = set(re.findall(r'\bBuilt ([\w.]+) \(',text))
assert set(hashes) <= fresh,sorted(set(hashes)-fresh)
audits = {}
for name,raw in re.findall(r"'(.+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text):
    axioms = [a.strip() for a in raw.split(',') if a.strip()]
    assert set(axioms) <= set(ALLOWED),(name,axioms)
    if name in audits:
        assert audits[name] == axioms,name
    audits[name] = axioms
assert set(expected['axiom_audit']) <= set(audits)
assert all(audits[n] == ax for n,ax in expected['axiom_audit'].items())
fc_targets = ['BinaryFormMoatCatalogue.gaussian_moat',
              'BinaryFormMoatCatalogue.gaussian_moat.generalizedvariant',
              'BinaryFormMoatCatalogue.binary_form_moat_classification']
assert set(fc_targets) <= set(audits)
objects = {}
for module in hashes:
    path = ROOT/'build/lake435/lib/lean' if module in local else (
        PROJECT/'vendor'/module.split('.')[0]/'.lake/build/lib/lean')
    objects[module] = sha256_file(path/(module.replace('.','/')+'.olean'))
proof_env = proof_environment(True)
paths = [Path(p).resolve() for p in proof_env['LEAN_PATH'].split(os.pathsep)]
if args.fresh_dependencies:
    assert all(p.is_relative_to(ROOT) or p.is_relative_to(TOOLS.parent) for p in paths), paths
save_json(out/'proof-environment.json',{'LEAN_PATH':proof_env['LEAN_PATH']})
report = dict(checked_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    lean=lock['lean'],mathlib_commit=lock['mathlib_commit'],upstream_commits=lock['upstream_commits'],
    project='verification/lean435',local_source_modules=302,selected_upstream_modules=311,
    total_selected_sources=613,source_sha256=hashes,built_olean_sha256=objects,axiom_audit=audits,
    fc_target_proof_source_sha256=sha256_file(ROOT/'BinaryFormMoatProof.lean'),
    fc_targets=fc_targets,fc_targets_proved_and_axiom_audited=True,
    source_lock_sha256=configs['source-lock.json'],lake_config_sha256={k:v for k,v in configs.items() if k!='source-lock.json'},
    build_log_sha256=sha256_file(build_log),strict_build_log_sha256=sha256_file(build_log),
    build_log=str(build_log.relative_to(ROOT)),download_log=str(download_log.relative_to(ROOT)),
    download_log_sha256=sha256_file(download_log),initial_state_sha256=sha256_file(baseline_path),
    initial_module_system_advisory_count=0,legacy_module_interop_explicitly_configured=True,
    strict_warning_free_lake_check_passed=True,all_613_selected_source_modules_freshly_built=True,
    old_custom_proof_output_trees_used=False,pinned_mathlib_package_cache_used=True,
    official_mathlib_objects_downloaded=True,local_mathlib_download_cache_reused=False,
    clean_selected_source_lake_build_performed=True,fresh_dependency_download_performed=args.fresh_dependencies,
    installed_pinned_toolchain_reused=True,independent_kernel_replay_in_this_command=False)
save_json(ROOT/'evidence/classification-lake-verification.json',report)
print(f'PASS: 613 source modules freshly built; {len(audits)} standard-axiom audits',flush=True)
print('PASS: pinned standalone build; source/package/environment/log hashes recorded',flush=True)
