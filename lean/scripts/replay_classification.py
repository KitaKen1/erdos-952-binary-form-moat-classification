#!/usr/bin/env python3
"""Export the proved main theorems and replay their full dependency proof in nanoda.

Uses the exporter and independent checker bundled in the exact compiler
toolchain. This does not run the older standalone LeanEval evaluation harness.
The default input is the immutable checked custom closure; --lake uses the
standalone Lake project's freshly built objects instead.
"""
import argparse
import datetime
import json
import os
import re
from pathlib import Path
import subprocess
import uuid
from classification_common import (ROOT,TOOLS,TARGETS,ALLOWED,sha256_file,
    save_json,proof_environment,proof_receipt,replay_certificate)

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--lake', action='store_true')
parser.add_argument('--reuse-certified-export', action='store_true',
                    help='reuse a successful replay only if fresh export and tool binaries match byte-for-byte')
parser.add_argument('--output-dir',default='build/classification-replay435')
parser.add_argument('--report',default='evidence/classification-replay.json')
parser.add_argument('--certificate',default='evidence/classification-replay.json')
args = parser.parse_args()
OUT = ROOT/args.output_dir/('run-'+uuid.uuid4().hex)
OUT.mkdir(parents=True,exist_ok=True)
receipt = proof_receipt(args.lake)
allowed,targets = ALLOWED,TARGETS
env = proof_environment(args.lake)
if not args.lake:
    for module,sha in receipt['cached_olean_sha256'].items():
        obj = ROOT/'build/unified435'/(module.replace('.','/')+'.olean')
        assert sha256_file(obj) == sha, module

export_path = OUT/('lake-main.ndjson' if args.lake else 'cached-main.ndjson')
command = [str(TOOLS/'leanexport'),'Moat.Conjectures','--']+targets
print('EXPORT: three original main theorems with all proof dependencies',flush=True)
with export_path.open('wb') as output, (OUT/'export-stderr.log').open('wb') as errors:
    subprocess.run(command,cwd=ROOT,env=env,stdout=output,stderr=errors,check=True,timeout=1800)
with export_path.open() as source:
    metadata = json.loads(next(source))
assert metadata['meta']['lean']['version'] == receipt['lean']
config = dict(export_file_path=str(export_path),use_stdin=False,permitted_axioms=allowed,
              unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,
              num_threads=4,print_success_message=True)
config_path = OUT/'nanoda-config.json'
config_path.write_text(json.dumps(config,indent=2)+'\n')
binary_hashes = {name:sha256_file(TOOLS/name)
                 for name in ['leanexport','nanoda_bin','leanchecker']}
export_sha = sha256_file(export_path)
previous = None
certificate_path = ROOT/args.certificate
if args.reuse_certified_export and certificate_path.exists():
    certificate_path,previous = replay_certificate(certificate_path)
reuse = (previous is not None and previous['export_sha256'] == export_sha
         and previous['binary_sha256'] == binary_hashes)
if reuse:
    certified_export = ROOT/previous['export_file']
    assert sha256_file(certified_export) == export_sha
results = dict(previous['results']) if reuse else {}
if reuse:
    print('PASS: fresh Lake export is byte-identical to the independently certified export; exact checker binaries unchanged',flush=True)
for name,command in ([] if reuse else [('nanoda',[str(TOOLS/'nanoda_bin'),str(config_path)]),
                     ('Lean default',[str(TOOLS/'leanchecker'),'--from-export',str(export_path)])]):
    print('REPLAY: '+name,flush=True)
    with (OUT/(name.replace(' ','-')+'.log')).open('wb') as log:
        result = subprocess.run(command,cwd=OUT,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=1800)
    results[name] = result.returncode
    if result.returncode:
        raise SystemExit(f'{name} rejected the export; see {OUT}')
    print('PASS: '+name+' accepts the complete main dependency export',flush=True)
log_dir = (ROOT/previous['export_file']).parent if reuse else OUT
nanoda_text = (log_dir/'nanoda.log').read_text()
counts = re.search(r'Checked (\d+) declarations with no typechecker errors, (\d+) pretty printer errors',nanoda_text)
assert counts
report = dict(checked_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    input='fresh standalone Lake objects' if args.lake else 'verified cached unified closure',
    parent_receipt_checked_at=receipt['checked_at'],lean=receipt['lean'],targets=targets,
    export_metadata=metadata,export_file=str(export_path.relative_to(ROOT)),
    export_sha256=export_sha,
    export_bytes=export_path.stat().st_size,permitted_axioms=allowed,
    unpermitted_axiom_hard_error=True,unsafe_permit_all_axioms=False,
    binary_sha256=binary_hashes,results=results,
    nanoda_checked_declarations=int(counts[1]),nanoda_typechecker_errors=0,
    nanoda_pretty_printer_errors=int(counts[2]),
    current_kernel_processes_executed=not reuse,certified_export_receipt_reused=reuse,
    reused_receipt=str(certificate_path.relative_to(ROOT)) if reuse else None,
    kernel_log_files={name:str((log_dir/(name+'.log')).relative_to(ROOT))
                      for name in ['nanoda','Lean-default']},
    independent_nanoda_kernel_replay_performed=True,new_tools_installed=False,
    standalone_lean_eval_harness_executed=False,fresh_dependency_download_performed=False,
    same_statement_comparator_performed=False)
report_path = ROOT/args.report
if not reuse and report_path.exists() and report_path.resolve() == certificate_path.resolve():
    # A successful executed receipt must remain immutable before being replaced.
    archive = OUT/('executed-receipt-'+sha256_file(report_path)+'.json')
    if archive.exists():
        assert archive.read_bytes() == report_path.read_bytes()
    else:
        archive.write_bytes(report_path.read_bytes())
save_json(report_path,report)
print('PASS: independent nanoda replay receipt saved',flush=True)
