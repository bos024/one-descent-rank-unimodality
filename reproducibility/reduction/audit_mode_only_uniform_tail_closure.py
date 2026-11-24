"""Finite COMPLETE minimal-crossing certificate and exact signed-window QA."""
from pathlib import Path
from random import Random
from collections import Counter
from math import comb
import json,time,hashlib
from audit_degree_boundary_CI_entrance import partitions,ci
from audit_binary_CI_infinite_padding_entrance import binary
from audit_joint_structure import fastconv
from audit_minimum_staircase_scaled_dyadic import arm_prefix
ROOT=Path(__file__).resolve().parent

def tail(V,u,alpha):
    h=sum(t-1 for t in V);L=ci(V);C=fastconv(L,binary(u-1));E=fastconv(L,[comb(u,j) for j in range(u+1)])
    base=h-2;off=u-1+alpha
    return [(C[n] if n<len(C) else 0)+(1 if n==base else 0)-
            (E[n-off] if 0<=n-off<len(E) else 0) for n in range(base,max(len(C),off+len(E))+1)]

def main():
    start=time.monotonic();ct=Counter();sha=hashlib.sha256();seeds=[];cert=set();seed_counts={}
    for u in range(1,14):
        seed_counts[u]=0
        for h in range(u+1,2*u+1):
            for ds in partitions(h):
                if len(ds)<2 or max(ds)>u or h-min(ds)>u:continue
                V=[x+1 for x in ds];seed_counts[u]+=1;clamp=(u+h)//2
                row=dict(u=u,V=V,h=h,padding_clamp=clamp,hosts=[])
                for alpha in range(1,clamp+2):
                    s=tail(V,u,alpha);g=[max(0,x) for x in s];M=g.index(max(g));margins=[]
                    assert all(g[n]<=g[n+1] for n in range(M)) and all(g[n]>=g[n+1] for n in range(M,len(g)-1))
                    for n in range(1,M):
                        z=g[n]**2-g[n-1]*g[n+1];assert z>=0;cert.add(z);margins.append(z);ct['complete_crossing_seed_LC_minors']+=1
                    row['hosts'].append(dict(alpha=alpha,first_tail_mode=M,margins=margins));ct['complete_crossing_seed_hosts']+=1
                    sha.update(json.dumps([u,V,alpha,s],separators=(',',':')).encode())
                seeds.append(row)
    assert len(seeds)==515
    rng=Random(20261029770)
    for trial in range(5000):
        # General UI g, LC only before its first mode; descending LC is NOT imposed.
        g=[1,rng.randint(2,12)]
        for _ in range(rng.randint(0,8)):
            low=g[-1];high=min(100000,g[-1]**2//g[-2])
            if high<low:break
            g.append(rng.randint(low,high))
        for _ in range(rng.randint(1,12)):g.append(rng.randint(1,g[-1]))
        M=g.index(max(g));assert all(g[n]**2>=g[n-1]*g[n+1] for n in range(1,M))
        t=rng.randint(2,24);B=fastconv(g,[1]*t);e=B.index(max(B))
        for n in range(1,e):
            assert B[n]**2>=B[n-1]*B[n+1];ct['generic_mode_only_uniform_minors']+=1
        signed=g+[-rng.randint(0,100000) for _ in range(rng.randint(1,12))]
        raw=[sum(signed[j] for j in range(max(0,n-t+1),min(n,len(signed)-1)+1)) for n in range(len(signed)+t-1)]
        pos=[max(0,x) for x in raw];ee=pos.index(max(pos))
        assert ee<=len(g)-1 and ee<=e
        for n in range(1,ee):assert pos[n]**2>=pos[n-1]*pos[n+1];ct['generic_signed_mode_only_minors']+=1
        ct['generic_window_contexts']+=1
    for trial in range(2000):
        u=rng.randint(1,20);alpha=rng.randint(1,30);V=sorted(rng.choices(range(3,25),k=rng.randint(1,8)));t=rng.randint(3,28)
        s=tail(V,u,alpha);Vp=sorted(V+[t]);sp=tail(Vp,u,alpha)
        for k in range(len(sp)):
            expected=sum(s[j] if j<len(s) else 0 for j in range(k,k+t))
            assert sp[k]==expected,('exact_insertion_tail',V,u,alpha,t,k,sp[k],expected)
            ct['exact_order_independent_signed_tail_window_reads']+=1
        g=[max(0,x) for x in s];M=g.index(max(g));premise=all(g[n]**2>=g[n-1]*g[n+1] for n in range(1,M))
        if premise:
            gp=[max(0,x) for x in sp];ee=gp.index(max(gp))
            for n in range(1,ee):assert gp[n]**2>=gp[n-1]*gp[n+1];ct['actual_arbitrary_insertion_mode_only_LC']+=1
            ct['actual_premise_satisfied_insertions']+=1
        F=arm_prefix(alpha,[2]*u+Vp,alpha+2*u+sum(Vp)+5)
        for k in range(min(len(sp),len(F)-sum(Vp))):
            n=sum(Vp)+k;assert sp[k]==F[n]-F[n-1];ct['literal_actual_sorted_tail_identifications']+=1
    out=dict(status='EXACT_QA_PASS_MODE_ONLY_WINDOWS_AND_COMPLETE_SMALL_BINARY_CROSSINGS',counts=dict(ct),seed_counts=seed_counts,
        complete_minimal_crossing_seeds=seeds,integer_margins=sorted(cert),state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='Complete515 minimal crossing seeds for 1<=u<=13, plus independent-to-be-rebuilt finite padding clamps, cover ONLY bounded exceptions to a written arbitrary-insertion theorem. This is pending formal/independent audit. Universal actual late-D LC for h>u at ALL u<=13 would follow; no C/A2/original UI conclusion.')
    (ROOT/'audit_mode_only_uniform_tail_closure.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['complete_minimal_crossing_seeds','integer_margins']}),flush=True)
    print(json.dumps(dict(seeds=len(seeds),unique_integer_margins=len(cert))),flush=True)

if __name__=='__main__':main()
