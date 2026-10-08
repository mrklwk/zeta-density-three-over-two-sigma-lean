#!/usr/bin/env python3
"""Offline fresh source build and runtime-enumerated production replay; no installation."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
import argparse,hashlib,json,os,re,subprocess,time

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def uncomment(text):
 out=[];i=0;depth=0
 while i<len(text):
  if text.startswith('/-',i):depth+=1;i+=2
  elif depth and text.startswith('-/',i):depth-=1;i+=2
  elif depth:out.append('\n' if text[i]=='\n' else ' ');i+=1
  elif text.startswith('--',i):
   j=text.find('\n',i);i=len(text) if j<0 else j
  else:out.append(text[i]);i+=1
 if depth:raise ValueError('Unclosed block comment')
 return ''.join(out)
def check_receipt(out,production):
 d=json.loads((out/'audit-receipt.json').read_text())
 roots=(out/'replay-roots.txt').read_text().splitlines();deps=(out/'proof-dependencies.txt').read_text().splitlines();final=(out/'final-theorem-dependencies.txt').read_text().splitlines()
 inventory=(out/'declaration-inventory.txt').read_text().splitlines();excluded=(out/'compiler-auxiliary-exclusions.txt').read_text().splitlines()
 duplicates=(out/'duplicate-declaration-origins.txt').read_text().splitlines()
 assert d['status']=='passed' and d['all_roots_present_after_replay'] is True
 assert d['production_modules']==len(production)
 assert d['replay_roots']==len(roots)==len(set(roots)) and roots
 assert d['replayed_declarations']==len(deps)==len(set(deps))
 assert d['final_density_closure']==len(final)==len(set(final))
 assert set(roots)<=set(deps) and set(final)<=set(deps)
 assert d['production_declarations']==len(inventory)
 assert d['production_theorems']==sum('|theorem=true|' in line for line in inventory)
 inventory_axioms={ax for line in inventory for ax in line.split('|')[-1].split(',') if ax}
 assert set(d['axioms'])==inventory_axioms
 assert d['excluded_compiler_auxiliaries']==len(excluded)
 assert d['duplicate_occurrences']==len(duplicates)
 assert set(d['axioms'])<=set(['propext','Classical.choice','Quot.sound'])
 names={line.split('|')[1] for line in inventory};skipped={line.split('|')[1] for line in excluded}
 assert set(roots)==names-skipped
 assert not skipped.intersection(deps)
 assert {'DensityStronger.density_bound','DensityStronger.twelfth_moment'}<=set(roots)
 return d

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--lean',required=True,type=Path);ap.add_argument('--packages',required=True,type=Path)
 ap.add_argument('--output',required=True,type=Path);ap.add_argument('--jobs',type=int,default=6)
 ap.add_argument('--direct-kernels',action='store_true',help='Use existing sibling leanexport/leanchecker/nanoda_bin/con-ron binaries')
 a=ap.parse_args();r=Path(__file__).resolve().parents[1];source=r/'lean';out=a.output.resolve();lean=a.lean.resolve();packages=a.packages.resolve()
 if out.exists():raise SystemExit('Output must be a new directory; no local object reuse.')
 if out.is_relative_to(r):raise SystemExit('Output must be outside the source repository.')
 if not 1<=a.jobs<=12:raise SystemExit('jobs must be between 1 and 12')
 out.mkdir(parents=True);(out/'lib').mkdir();(out/'modules').mkdir();start=time.monotonic()
 record={'status':'running','repository':str(r),'output':str(out),'local_olean_reuse':False,'dependency_cache_source_binding_verified':False,'dependency_semantic_trust':'Imported mathematical definitions are trusted to correspond to pinned dependency sources; source HEAD checks and kernel replay alone do not establish that correspondence.','network_or_install':False}
 def save():(out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
 def read(cmd,cwd):return subprocess.check_output(list(map(str,cmd)),cwd=cwd,text=True,stderr=subprocess.STDOUT)
 save()
 try:
  version=read([lean,'--version'],r);assert '4.35.0-rc2' in version and '11acb17ec6b07a8f9e9173e6845197929540936b' in version
  record['lean_version']=version.strip();libs=[];pins=[]
  for p in json.loads((source/'lake-manifest.json').read_text())['packages']:
   d=packages/p['name'];assert read(['git','rev-parse','HEAD'],d).strip()==p['rev']
   assert not read(['git','status','--porcelain=v1','--untracked-files=no'],d).strip()
   lib=d/'.lake/build/lib/lean'
   if lib.is_dir():libs.append(lib)
   pins.append({'name':p['name'],'revision':p['rev'],'tracked_source_clean':True,'library':str(lib) if lib.is_dir() else None})
  assert (packages/'mathlib/lean-toolchain').read_text().strip()==(source/'lean-toolchain').read_text().strip();record['dependencies']=pins
  sources={'.'.join(p.relative_to(source).with_suffix('').parts):p for p in source.rglob('*.lean') if '.lake' not in p.parts}
  support={'MathCollab','MathCollab.Density.Audit','MathCollab.FullAudit','Challenge'}
  production=sorted(set(sources)-support);record['source_roles']={'production':production,'support':sorted(set(sources)&support)}
  clean={m:uncomment(p.read_text()) for m,p in sources.items()}
  for m in production:
   assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|initialize)\b|skipKernelTC',clean[m]),m
  assert len(re.findall(r'\bsorry\b',clean['Challenge']))==2
  deps={m:set(re.findall(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+([\w.]+)',t,re.M))&sources.keys() for m,t in clean.items()}
  assert not any('Challenge' in ds for m,ds in deps.items() if m!='Challenge')
  snapshot={str(p.relative_to(r)):sha(p) for p in sources.values()};(out/'source-hashes.json').write_text(json.dumps(snapshot,indent=2)+'\n')
  env=dict(os.environ);env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','');env['LEAN_PATH']=os.pathsep.join(map(str,[out/'lib',*libs]))
  (out/'lean-path.txt').write_text(env['LEAN_PATH']+'\n');(out/'project-modules.txt').write_text('\n'.join(production)+'\n')
  template=(r/'scripts/verification/IndependentStrongerReplay.lean').read_text()
  generated=template.replace('-- PROJECT_IMPORTS are generated from the current source inventory by verify.py.','\n'.join('public import '+m for m in production))
  (out/'RuntimeReplay.lean').write_text(generated)
  records=[];done=set();pending=set(sources);running={}
  def compile_one(m):
   obj=out/'lib'/Path(*m.split('.')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
   cmd=[str(lean),'-o',str(obj),str(sources[m].relative_to(source))]
   if m!='Challenge':cmd.insert(1,'-DwarningAsError=true')
   if m.startswith(('GuthMaynard.','WeylPort.')):cmd.insert(1,'-DautoImplicit=false')
   begin=time.monotonic()
   with (out/'modules'/(m+'.log')).open('w') as log:c=subprocess.run(cmd,cwd=source,env=env,stdout=log,stderr=subprocess.STDOUT)
   return {'module':m,'command':cmd,'exit_code':c.returncode,'seconds':round(time.monotonic()-begin,3)}
  with ThreadPoolExecutor(max_workers=a.jobs) as pool:
   while pending or running:
    for m in sorted(m for m in pending if deps[m]<=done)[:a.jobs-len(running)]:pending.remove(m);running[pool.submit(compile_one,m)]=m
    assert running,'Unresolved/cyclic imports'
    finished,_=wait(running,return_when=FIRST_COMPLETED)
    for f in finished:
     m=running.pop(f);rec=f.result();records.append(rec);(out/'module-builds.json').write_text(json.dumps(records,indent=2)+'\n')
     print(f"{len(records)}/{len(sources)} {m}: exit {rec['exit_code']}",flush=True)
     assert rec['exit_code']==0,'Build failed: '+m;done.add(m)
  record['fresh_local_modules']=len(records);save();checks=[]
  def run(name,cmd,cwd=out,output=None):
   begin=time.monotonic();path=output or out/(name+'.log')
   with path.open('w') as log:c=subprocess.run(list(map(str,cmd)),cwd=cwd,env=env,stdout=log,stderr=subprocess.PIPE,text=True)
   (out/(name+'.stderr')).write_text(c.stderr)
   checks.append({'name':name,'command':list(map(str,cmd)),'cwd':str(cwd),'exit_code':c.returncode,'seconds':round(time.monotonic()-begin,3)})
   record['checks']=checks;save();assert c.returncode==0,'Check failed: '+name
   print(name+': PASS',flush=True)
  for name in ['BaselineSemanticChecks','NativeSemanticChecks','IndependentStrongerSemantics','IndependentStrongerStatements']:
   run(name,[lean,'-DwarningAsError=true',r/'scripts/verification'/(name+'.lean')])
  run('RuntimeReplay',[lean,'-DwarningAsError=true',out/'RuntimeReplay.lean'])
  record['runtime_replay']=check_receipt(out,production);save()
  comparisons=[]
  for declaration in ['DensityStronger.density_bound','DensityStronger.twelfth_moment']:
   paths=[]
   for module in ['Challenge','Solution']:
    path=out/(module+'-'+declaration+'.type.txt');paths.append(path)
    run(module+'-'+declaration,[lean,'--run',r/'scripts/verification/InterfaceType.lean',module,declaration],output=path)
   assert paths[0].read_bytes()==paths[1].read_bytes()
   comparisons.append({'declaration':declaration,'exact_type_match':True,'type_sha256':sha(paths[0])})
  (out/'type-comparisons.json').write_text(json.dumps(comparisons,indent=2)+'\n')
  if a.direct_kernels:
   export=out/'solution.export.jsonl';bins=lean.parent
   run('export',[bins/'leanexport','Solution','--','DensityStronger.density_bound','DensityStronger.twelfth_moment'],output=export)
   (out/'nanoda.json').write_text(json.dumps({'use_stdin':False,'export_file_path':str(export),'permitted_axioms':['propext','Classical.choice','Quot.sound'],'unpermitted_axiom_hard_error':True,'num_threads':a.jobs,'nat_extension':True,'string_extension':True},indent=2))
   run('leanchecker',[bins/'leanchecker','--from-export',export]);run('nanoda',[bins/'nanoda_bin',out/'nanoda.json']);run('con-ron',[bins/'con-ron','--jobs=2',export])
   record['direct_kernels']={'export_sha256':sha(export),'export_bytes':export.stat().st_size,'sandboxed_comparator':False,'binaries':{n:sha(bins/n) for n in ['leanexport','leanchecker','nanoda_bin','con-ron']}}
  for path,h in snapshot.items():assert sha(r/path)==h,'Source changed during verification: '+path
  record.update(status='passed',seconds=round(time.monotonic()-start,3));save();print('PASS: fresh build, runtime production replay and exact public type comparison.',flush=True)
 except BaseException as e:
  record.update(status='failed',error=str(e),seconds=round(time.monotonic()-start,3));save();raise
if __name__=='__main__':main()
