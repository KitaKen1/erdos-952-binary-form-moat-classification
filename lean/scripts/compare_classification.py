#!/usr/bin/env python3
"""Compare the exact pre-removal statement/definitions to the proved classification.

The generated challenge is the byte-exact original file, with its original sorry.
It is statement input, never counted as a verified proof or an allowed axiom.
The stock bundled Lake comparator checks all three statements, every referenced
definition and kernel primitive; its axiom audit checks only the proved solution.
Independent kernel replay is recorded separately by replay_classification.py.
"""
import argparse
import datetime
import json
import os
from pathlib import Path
import subprocess
from classification_common import (ROOT,TOOLS,TARGETS,ALLOWED,sha256_file,
                                   save_json,proof_environment,proof_receipt)

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--lake',action='store_true',help='use only the pinned standalone Lake environment')
parser.add_argument('--output-dir',default='build/classification-statement435')
parser.add_argument('--report',default='evidence/classification-statement-comparison.json')
args = parser.parse_args()
OUT = ROOT/args.output_dir
OUT.mkdir(parents=True,exist_ok=True)
receipt = proof_receipt(args.lake)
lock = json.loads((ROOT/'evidence/classification-statement-lock.json').read_text())
source = (ROOT/'Moat/Conjectures.lean').read_text()
source = source.replace('import Integrations.IrreducibleFiniteSieve435\n','',1)
source = source.replace('The irreducible branch, proved by the finite prime sieve and the lattice ray bridge.',
                        'The remaining mathematical proof obligation after the complete algebraic reduction.',1)
source = source.replace('  exact GeometryIntegration.irreducible_homogenization_uniformMoat_verified p hp hdeg','  sorry',1)
source = source.replace('The all-degree sufficiency direction after the complete algebraic reduction.',
                        'The all-degree sufficiency direction, conditional on the unproved irreducible case above.',1)
source = source.replace('The classification for every nonzero positive-degree homogeneous binary form.',
                        'Candidate classification; its sufficiency direction remains unproved.',1)
source = source.split('\n\n#print axioms')[0]+'\n'
challenge = OUT/'OriginalClassification435.lean'
challenge.write_text(source)
assert sha256_file(challenge) == lock['source_before_sha256']
env = proof_environment(args.lake)
env['LEAN_PATH'] = str(OUT)+os.pathsep+env['LEAN_PATH']
with (OUT/'challenge.log').open('wb') as log:
    subprocess.run([str(TOOLS/'lean'),'-o',str(OUT/'OriginalClassification435.olean'),str(challenge)],
                   cwd=OUT,env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=300)
targets,allowed = TARGETS,ALLOWED
# This is exactly Lake.Check.primitiveTargets at the pinned compiler source.
primitives = ['Nat.add','Nat.sub','Nat.mul','Nat.pow','Nat.gcd','Nat.div','Nat.mod',
    'Nat.beq','Nat.ble','Nat.land','Nat.lor','Nat.xor','Nat.shiftLeft','Nat.shiftRight',
    'String.ofList','Char.ofNat','List','eagerReduce','Nat','String','String.mk','Char',
    'optParam','autoParam','semiOutParam','outParam']
quotients = ['Quot','Quot.mk','Quot.lift','Quot.ind']
exports = {}
for kind,module in [('challenge','OriginalClassification435'),('solution','Moat.Conjectures')]:
    path = OUT/(kind+'.ndjson')
    print('EXPORT: '+kind,flush=True)
    with path.open('wb') as output,(OUT/(kind+'-export.log')).open('wb') as errors:
        subprocess.run([str(TOOLS/'leanexport'),module,'--']+targets+allowed+primitives+quotients,
                       cwd=OUT,env=env,stdout=output,stderr=errors,check=True,timeout=600)
    exports[kind] = path
def array(names):
    return '#['+','.join(json.dumps(n) for n in names)+'].map String.toName'
checker = OUT/'CompareExports.lean'
checker.write_text('''import Lake.Check.Compare
import Lake.Check.Axioms
import LeanExport.Parse

open Lean
def main (args : List String) : IO UInt32 := do
  let [challengePath, solutionPath] := args | throw <| IO.userError "two exports required"
  let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk challengePath .read)
  let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk solutionPath .read)
  let targets := '''+array(targets)+'''
  let legalAxioms := '''+array(allowed)+'''
  let primitive := '''+array(primitives)+'''
  IO.ofExcept <| Lake.Check.compareAt challenge solution (targets ++ legalAxioms) #[] primitive
  IO.ofExcept <| Lake.Check.checkAxioms solution targets #[] legalAxioms
  IO.println "PASS: exact original theorem statements, all referenced definitions and kernel primitives match"
  IO.println "PASS: proved solution dependency graph uses only the three standard axioms"
  return 0
''')
trusted_env = os.environ.copy()
trusted_env.pop('LEAN_PATH',None)
trusted_env['PATH'] = str(TOOLS)+os.pathsep+trusted_env.get('PATH','')
print('COMPARE: stock bundled Lake compareAt/checkAxioms',flush=True)
with (OUT/'comparison.log').open('wb') as log:
    subprocess.run([str(TOOLS/'lean'),'--run',str(checker),str(exports['challenge']),str(exports['solution'])],
                   cwd=OUT,env=trusted_env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=600)
report = dict(checked_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    parent_receipt_checked_at=receipt['checked_at'],lean=receipt['lean'],targets=targets,
    input='fresh standalone Lake objects' if args.lake else 'verified cached unified closure',
    output_directory=str(OUT.relative_to(ROOT)),
    old_custom_proof_output_trees_used=not args.lake,
    challenge_matches_byte_exact_original_source=True,original_source_sha256=lock['source_before_sha256'],
    checker='Stock Lake.Check.compareAt and Lake.Check.checkAxioms in the bundled pinned toolchain',
    challenge_proof_is_unproved_statement_input_only=True,challenge_placeholder_accepted_as_solution_axiom=False,
    exact_original_theorem_statements_and_all_referenced_definitions_match=True,
    kernel_primitive_definitions_match=True,solution_axioms_standard=True,
    permitted_axioms=allowed,export_sha256={k:sha256_file(p) for k,p in exports.items()},
    checker_source_sha256=sha256_file(checker),
    comparator_and_axiom_checks_exit_code=0,independent_kernel_replay_in_this_command=False,
    standalone_lean_eval_harness_executed=False,new_tools_installed=False)
save_json(ROOT/args.report,report)
print('PASS: original-statement/definition/primitive comparator receipt saved',flush=True)
