"""Exact exploratory ordinary-head falsifier. No universal inference."""
from pathlib import Path
from random import Random
from collections import Counter
import json,time,hashlib

def reference(V):
    N=sum(V)+3
    f=[1,1]
    for n in range(2,N+1):f.append(f[-1]+f[-2])
    for t in V:
        g=[1];window=0
        for n in range(1,N+1):
            window+=f[n-1]-(f[n-t-1] if n>t else 0)
            g.append(window)
        f=g
    return f

def main():
    start=time.monotonic();counts=Counter();bad={};sha=hashlib.sha256();rng=Random(117934)
    words=[([3]*r+[4]*s,'three_four') for r in range(1,65) for s in range(1,65)]
    words += [(sorted(rng.choices(range(3,20),k=rng.randint(4,40))),'general') for _ in range(1500)]
    for V,kind in words:
        f=reference(V);W=sum(V);a=len(V)+3
        if kind=='three_four' and len(V)<8:continue
        failures=[]
        for n in range(a,W+1):
            margin=f[n]*f[n]-f[n-1]*f[n+1];counts[kind+'_minors']+=1
            if margin<0:failures.append((n,margin))
        if failures:
            counts[kind+'_bad_hosts']+=1
            if kind not in bad:bad[kind]=dict(V=V,failures=failures[:5],last_bad=failures[-1])
        counts[kind+'_hosts']+=1
        sha.update(json.dumps([V,f],separators=(',',':')).encode())
    out=dict(status='EXACT_FINITE_DIAGNOSTIC_ONLY',counts=dict(counts),counterexamples=bad,
        sha256=sha.hexdigest(),seconds=time.monotonic()-start)
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)
if __name__=='__main__':main()
