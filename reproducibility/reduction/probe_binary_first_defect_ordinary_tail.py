"""Exact finite test of a new conditional ordinary-tail target."""
from pathlib import Path
from collections import Counter
from random import Random
import json,time

def arm(alpha,U):
    N=alpha+sum(U);f=[1]*(alpha+1)
    for t in U:
        g=[1]+[0]*(len(f)+t-1);v=0
        for n in range(1,len(g)):
            v+=(f[n-1] if n-1<len(f) else 0)-(f[n-t-1] if 0<=n-t-1<len(f) else 0)
            g[n]=v
        f=g
    return f+[0,0]

def main():
    start=time.monotonic();counts=Counter();bad={};rng=Random(553461)
    contexts=[]
    for r in range(1,29):
        for s in range(1,29):
            h=2*r+3*s
            for u in sorted(set([1,2,3,4,5,h//3,h//2,h-2,h-1,h])):
                for alpha in [1,2,3,7]:contexts.append((alpha,u,[3]*r+[4]*s,'three_four'))
    for _ in range(5000):
        V=sorted(rng.choices(range(3,22),k=rng.randint(1,24)));h=sum(t-1 for t in V)
        u=rng.randint(1,h);contexts.append((rng.choice([1,2,3,10]),u,V,'general'))
    for alpha,u,V,kind in contexts:
        f=arm(alpha,[2]*u+V);a=u+len(V)+2
        for n in range(a,len(f)-1):
            v=f[n]*f[n]-f[n-1]*f[n+1];counts[kind+'_minors']+=1
            if v<0:
                counts[kind+'_bad_hosts']+=1
                if kind not in bad:bad[kind]=dict(alpha=alpha,u=u,V=V,n=n,a=a,triple=f[n-1:n+2],margin=v)
                break
        counts[kind+'_hosts']+=1
    out=dict(status='EXACT_FINITE_DIAGNOSTIC_ONLY',counts=dict(counts),counterexamples=bad,seconds=time.monotonic()-start)
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
