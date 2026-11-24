"""Verify the complete research supplement with Python's standard library (3.10+)."""
import argparse, hashlib, json, os, re, runpy, shutil, subprocess, sys, tempfile
from pathlib import Path

BASE=Path(__file__).resolve().parent
HISTORICAL=[
    ('verify_first_missing_twelve_head_certificate.py','first_missing_twelve_head_certificate_verification.json'),
    ('verify_complete_mixed_unrestricted_C_original.py','complete_mixed_unrestricted_C_original_verification.json'),
    ('verify_one_hereditary_C_arm_arbitrary_other.py','one_hereditary_C_arm_arbitrary_other_verification.json')]
ACTUAL=[
    ('audit_depth_slack_bridge.py','depth_slack_actual_audit.json'),
    ('verify_literal_principal_ideals.py','literal_principal_ideals_audit.json')]
LEAN={'DepthSlackTransport':19,'DepthSlackArmIdentities':7}
AXIOMS={'propext','Classical.choice','Quot.sound'}

def read(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def digest(path):
    h=hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1<<20),b''):
            h.update(block)
    return h.hexdigest()

def require(ok,message):
    if not ok:
        raise ValueError(str(message))

def compare_lean(name,log):
    source=(BASE/(name+'.lean')).read_text(encoding='utf-8-sig')
    require(not re.search(r'\b(?:sorry|axiom|unsafe|native_decide)\b',source),name)
    require(not re.search(r'error:|warning:|sorryAx|ofReduceBool',log),name+' log diagnostics')
    expected=re.findall(r'^#print axioms (\S+)',source,re.M)
    printed=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
    require(len(expected)==len(set(expected))==LEAN[name],name+' declaration count')
    require([n for n,_ in printed]==expected,name+' reported theorem names')
    for n,axioms in printed:
        require(set(a.strip() for a in axioms.split(',') if a.strip())<=AXIOMS,n)

def inventory():
    manifest=read(BASE/'MANIFEST.json')
    for rel,expected in manifest['files'].items():
        file=(BASE/rel).resolve()
        require(file.is_relative_to(BASE) and file.is_file(),rel)
        require(digest(file)==expected,'hash mismatch for '+rel)
    for role in LEAN:
        compare_lean(role,(BASE/(role+'.log')).read_text(encoding='utf-8-sig'))
    idx=read(BASE/'checks'/'dependency_index.json')
    checks=0
    root=BASE/'reduction'
    for name,refs in idx['recorded_digests'].items():
        data=read(root/name)
        def walk(obj):
            if isinstance(obj,dict):
                for k,v in obj.items():
                    if k in refs and isinstance(v,str) and re.fullmatch('[0-9a-fA-F]{64}',v):
                        yield k,v
                    if isinstance(v,(dict,list)):yield from walk(v)
            elif isinstance(obj,list):
                for v in obj:
                    if isinstance(v,(dict,list)):yield from walk(v)
        for other,value in walk(data):
            require(manifest['files']['reduction/'+other]==value.lower(),(name,other))
            checks+=1
    require(checks==idx['archived_sha256_comparisons'],('historical comparison count',checks))
    print(f"Verified {len(manifest['files'])} files, {checks} archived digest comparisons, and {sum(LEAN.values())} new Lean theorem reports.",flush=True)

def replay_archived(script,report,directory):
    root=BASE/'reduction'
    reference=read(root/report)
    for name in reference['sha256']:
        require(Path(name).name==name,name)
        shutil.copyfile(root/name,directory/name)
    # The scripts read the published sources and write only into this temporary directory.
    os.environ['ONE_DESCENT_REPLAY_DIR']=str(directory)
    sys.path[:0]=[str(root),str(BASE/'foundations')]
    runpy.run_path(str(root/script),run_name='__main__')
    actual=read(directory/report)
    for key in reference.keys()|actual.keys():
        if key!='seconds':
            require(reference[key]==actual[key],(script,key))

def isolated(command,directory):
    process=subprocess.run(command,cwd=directory,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},
         stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    if process.returncode:
        raise RuntimeError(process.stdout.decode(errors='replace')[-9000:])

def replay():
    for script,report in ACTUAL:
        with tempfile.TemporaryDirectory() as td:
            t=Path(td)
            for source,_ in ACTUAL:
                shutil.copyfile(BASE/'checks'/source,t/source)
            isolated([sys.executable,'-B',str(t/script)],t)
            require(read(t/report)==read(BASE/'checks'/report),script)
            print('Replayed '+script,flush=True)
    for script,report in HISTORICAL:
        with tempfile.TemporaryDirectory() as td:
            t=Path(td)
            isolated([sys.executable,'-B',str(Path(__file__).resolve()),'--archived-worker',script,report,str(t)],t)
            print('Replayed '+script,flush=True)

    script=BASE/'checks'/'check_peak_boundary.py'
    result=subprocess.run([sys.executable,'-B',str(script)],capture_output=True,check=True)
    require(json.loads(result.stdout)==read(BASE/'checks'/'peak_boundary_audit.json'),script.name)
    print('Replayed '+script.name,flush=True)

def run_lean(project):
    for name in LEAN:
        command=['lake','env','lean',str(BASE/(name+'.lean'))] if project else ['lean',str(BASE/(name+'.lean'))]
        result=subprocess.run(command,cwd=project or BASE,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        text=result.stdout.decode('utf-8',errors='replace')
        require(result.returncode==0,text[-4500:])
        compare_lean(name,text)
        print('Type-checked '+name+'.lean',flush=True)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay',action='store_true',help='repeat the two composition audits, three historical checks, and the strict-peak boundary check')
    parser.add_argument('--lean',action='store_true',help='call lean using an existing Mathlib environment')
    parser.add_argument('--mathlib-project',type=Path,help='use lake env lean in the given Mathlib project')
    parser.add_argument('--archived-worker',nargs=3,help=argparse.SUPPRESS)
    args=parser.parse_args()
    if args.archived_worker:
        script,report,directory=args.archived_worker
        require((script,report) in HISTORICAL,script)
        target=Path(directory).resolve()
        require(target!=BASE and not any(target.iterdir()),'worker requires an empty working directory')
        replay_archived(script,report,target)
        return
    inventory()
    if args.replay:replay()
    if args.lean or args.mathlib_project:run_lean(args.mathlib_project)

if __name__=='__main__':
    main()
