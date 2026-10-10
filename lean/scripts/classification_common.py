"""Pinned-toolchain helpers shared by portable classification verification."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT/'verification/lean435'
TOOLS = Path.home()/'.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin'
TARGETS = ['BinaryFormMoat.irreducible_homogenization_uniformMoat',
           'BinaryFormMoat.uniformMoat_of_not_isLinearPower',
           'BinaryFormMoat.classification']
ALLOWED = ['propext','Classical.choice','Quot.sound']

def sha256_file(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda:stream.read(8*1024*1024),b''):
            digest.update(block)
    return digest.hexdigest()

def save_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True,exist_ok=True)
    temporary = path.with_suffix(path.suffix+'.tmp')
    temporary.write_text(json.dumps(value,indent=2,ensure_ascii=False)+'\n')
    temporary.replace(path)

def proof_environment(lake):
    env = os.environ.copy()
    env['PATH'] = str(TOOLS)+os.pathsep+env.get('PATH','')
    env['LEAN_ABORT_ON_PANIC'] = '1'
    if lake:
        env.pop('LEAN_PATH',None)
        code = ('import json,os; print(json.dumps({k:os.environ[k] for k in '
                "['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT'] if k in os.environ}))")
        raw = subprocess.check_output([str(TOOLS/'lake'),'env','python3','-c',code],
                                      cwd=PROJECT,env=env,text=True,timeout=120)
        env.update(json.loads(raw))
        paths = {Path(p).resolve() for p in env['LEAN_PATH'].split(os.pathsep)}
        assert (ROOT/'build/lake435/lib/lean').resolve() in paths
        assert all((ROOT/'build'/name).resolve() not in paths for name in
                   ['unified435','pfr435','harper435','brouwer435','tauceti435'])
    else:
        raise ValueError('This source-only publication bundle requires --lake')
    return env

def proof_receipt(lake):
    name = 'classification-lake-verification' if lake else 'unified-verification'
    receipt = json.loads((ROOT/'evidence'/(name+'.json')).read_text())
    assert receipt['lean'] == '4.35.0-rc3'
    for target in TARGETS:
        assert set(receipt['axiom_audit'][target]) == set(ALLOWED), target
    return receipt

def replay_certificate(path):
    """Follow immutable reuse links to an actually executed kernel receipt.

    Every hop must describe the same export, targets, checker binaries and legal
    axioms. A changed export/toolchain is handled by executing the checkers again.
    Missing, inconsistent or cyclic certificates are rejected.
    """
    path = Path(path).resolve()
    seen = set()
    first = None
    while True:
        assert path not in seen, 'Cyclic replay certificate'
        seen.add(path)
        receipt = json.loads(path.read_text())
        assert receipt['results'] == {'nanoda':0,'Lean default':0}
        assert receipt['independent_nanoda_kernel_replay_performed']
        assert receipt['targets'] == TARGETS and receipt['permitted_axioms'] == ALLOWED
        assert receipt['unpermitted_axiom_hard_error'] and not receipt.get('unsafe_permit_all_axioms',False)
        if first is None:
            first = receipt
        for key in ['export_sha256','binary_sha256','targets','permitted_axioms']:
            assert receipt[key] == first[key], (path,key)
        if not receipt.get('certified_export_receipt_reused',False):
            assert receipt.get('current_kernel_processes_executed',True)
            return path,receipt
        reference = Path(receipt['reused_receipt'])
        path = (reference if reference.is_absolute() else ROOT/reference).resolve()
