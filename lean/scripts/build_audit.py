#!/usr/bin/env python3
"""Run the full fresh-download source build, original comparison and two kernels."""
import argparse
from pathlib import Path
import subprocess
import sys
root=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--resume',action='store_true')
a=p.parse_args()
commands=[['verify_classification_project.py','--fresh-dependencies']+(['--resume'] if a.resume else []),
          ['compare_classification.py','--lake'],['replay_classification.py','--lake']]
for command in commands:
    subprocess.run([sys.executable,str(root/'scripts'/command[0])]+command[1:],cwd=root,check=True)
print('PASS: complete source build, original statement comparison and both kernel checks')
