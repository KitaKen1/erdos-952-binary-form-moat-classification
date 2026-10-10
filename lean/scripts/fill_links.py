#!/usr/bin/env python3
"""Prepare fixed-commit proof/browser links after a public commit exists.

This edits local files only. It does not push, post, license or create a repo.
The caller must supply the already-public repository, commit and paper URL.
"""
import argparse
import json
from pathlib import Path
import re
from urllib.parse import quote,urlparse

root = Path(__file__).resolve().parents[2]
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('repository')
p.add_argument('commit')
p.add_argument('--paper-url',required=True)
p.add_argument('--write',action='store_true',help='set fixed-commit proof links in the local FC files; otherwise print only')
a = p.parse_args()
repo = urlparse(a.repository.rstrip('/'))
assert repo.scheme == 'https' and repo.netloc == 'github.com'
assert not repo.query and not repo.fragment and re.fullmatch(r'/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+',repo.path)
assert re.fullmatch(r'[0-9a-f]{40}',a.commit)
paper = urlparse(a.paper_url)
assert paper.scheme == 'https' and paper.netloc and not paper.netloc.endswith('.invalid')
main = root/'lean/Moat/Conjectures.lean'
line = next(i for i,t in enumerate(main.read_text().splitlines(),1) if t.startswith('theorem classification '))
proof = a.repository.rstrip('/')+'/blob/'+a.commit+'/lean/Moat/Conjectures.lean#L'+str(line)
links = dict(repository=a.repository.rstrip('/'),commit=a.commit,paper=a.paper_url,proof=proof)
links['browser_checks'] = {name:'https://live.lean-lang.org/#url='+quote(
    'https://raw.githubusercontent.com'+repo.path+'/'+a.commit+'/lean4web/'+name+'.lean',safe='')
    for name in ['BinaryFormMoatLean4Web']}
if a.write:
    for name in ['GaussianMoat', 'BinaryFormMoatClassification']:
        fc = root/'FClikelean'/(name+'.lean')
        text = fc.read_text()
        old = '[complete proof](../lean/Moat/Conjectures.lean)'
        assert old in text, 'Expected the local complete-proof reference in '+name
        fc.write_text(text.replace(old, '[complete proof]('+proof+')'))
    (root/'lean/evidence/publication-links.json').write_text(json.dumps(links,indent=2)+'\n')
print(json.dumps(links,indent=2))
print('Local link preparation only. Recheck FC statements after changing their references.')
