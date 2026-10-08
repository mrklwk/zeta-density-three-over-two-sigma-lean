#!/usr/bin/env python3
"""Tamper tests against an actual successful runtime replay receipt, without rerunning proofs."""
from pathlib import Path
import argparse,json,tempfile,shutil,importlib.util
spec=importlib.util.spec_from_file_location('verifier',Path(__file__).with_name('verify.py'));v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
ap=argparse.ArgumentParser();ap.add_argument('evidence',type=Path);a=ap.parse_args();src=a.evidence
production=(src/'project-modules.txt').read_text().splitlines()
files=['audit-receipt.json','replay-roots.txt','proof-dependencies.txt','final-theorem-dependencies.txt','declaration-inventory.txt','compiler-auxiliary-exclusions.txt','duplicate-declaration-origins.txt']
v.check_receipt(src,production)
cases=['wrong_root_count','additional_axiom','missing_root','duplicated_dependency','wrong_theorem_count','false_status']
results={'unaltered_receipt':'accepted','mutations':{}}
for case in cases:
 with tempfile.TemporaryDirectory(prefix='density-receipt-test-') as temp:
  p=Path(temp)
  for f in files:shutil.copy2(src/f,p/f)
  d=json.loads((p/'audit-receipt.json').read_text())
  if case=='wrong_root_count':d['replay_roots']+=1
  elif case=='additional_axiom':d['axioms'].append('sorryAx')
  elif case=='wrong_theorem_count':d['production_theorems']+=1
  elif case=='false_status':d['status']='running'
  elif case=='missing_root':
   roots=(p/'replay-roots.txt').read_text().splitlines();roots.remove('DensityStronger.density_bound');d['replay_roots']-=1;(p/'replay-roots.txt').write_text('\n'.join(roots)+'\n')
  elif case=='duplicated_dependency':
   deps=(p/'proof-dependencies.txt').read_text().splitlines();deps.append(deps[0]);d['replayed_declarations']+=1;(p/'proof-dependencies.txt').write_text('\n'.join(deps)+'\n')
  (p/'audit-receipt.json').write_text(json.dumps(d))
  try:v.check_receipt(p,production)
  except (AssertionError,KeyError,ValueError):results['mutations'][case]='rejected'
  else:raise SystemExit('Malformed receipt accepted: '+case)
print(json.dumps(results,indent=2))
