"""Exact automatic-cone QA and COMPLETE five-tail/u8 literal-C entrance."""
from pathlib import Path
from random import Random
from itertools import accumulate
from collections import Counter
import json,time,hashlib
from audit_degree_boundary_CI_entrance import partitions
from audit_mode_only_uniform_tail_closure import tail
from audit_minimum_staircase_scaled_dyadic import arm_prefix
ROOT=Path(__file__).resolve().parent

def main():
    start=time.monotonic();rng=Random(20261029772);ct=Counter();sha=hashlib.sha256();contexts=[];cert=set();profiles=[]
    for h in range(10,23):
        for ds in partitions(h):
            V=[x+1 for x in ds]
            if h+len(ds)>32 and max(V)<16:profiles.append(V)
    assert profiles==[[3]*11]
    for V in profiles:
        u=8;h=sum(t-1 for t in V);W=sum(V);clamp=(u+h)//2+1;assert clamp==16
        upper=len(V)+2+(3*u-4+h+1)//2
        for alpha in range(1,clamp+1):
            F=arm_prefix(alpha,[2]*u+V,alpha+2*u+W+5);G=list(accumulate(F))
            D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];ell=D.index(max(D));margins=[];keys=[]
            assert ell<=upper
            for n in range(W+1,ell+1):
                for k in range(1,n-2):
                    M=G[k]*D[n-1]-G[k-1]*D[n];assert M>=0
                    cert.add(M);margins.append(M);keys.append([n,k]);ct['complete_u8_all_literal_C_shifts']+=1
            contexts.append(dict(u=u,V=V,alpha=alpha,clamp=clamp,first_D_mode=ell,upper_mode_bound=upper,keys=keys,margins=margins))
            sha.update(json.dumps([V,alpha,F,D],separators=(',',':')).encode());ct['complete_u8_actual_hosts']+=1
    infinite_edge=None
    for V in profiles:
        s=tail(V,8,16);assert s[0]==5109250 and s[1]==5076760
        infinite_edge=dict(u=8,V=V,W=sum(V),alpha_infinite_representative=16,previous=s[0],current=s[1],margin=s[0]-s[1])
        assert infinite_edge['margin']==32490;cert.add(infinite_edge['margin'])
    for trial in range(3500):
        u=rng.randint(1,45);V=sorted(rng.choices(range(3,3*u+3),k=rng.randint(1,14)));h=sum(t-1 for t in V)
        if not (h>=3*u-1 or max(V)>=2*u):continue
        for alpha in {1,2,rng.randint(1,u+h),u+h+2}:
            s=tail(V,u,alpha);g=[max(0,x) for x in s]
            for n in range(1,len(g)):
                assert g[n]<=g[n-1],('automatic_cone',u,V,alpha,n,g[n-1:n+1]);ct['automatic_cone_nonincreasing_tail_edges']+=1
            ct['automatic_cone_actual_contexts']+=1
    for u in range(1,41):
        # Exact IMPROVED h=3u-1 and t=2u boundaries.
        degree=3*u-1
        V=([4]+[3]*((degree-3)//2)) if degree%2 else [3]*(degree//2)
        assert sum(t-1 for t in V)==3*u-1
        for alpha in {1,2,u+1,4*u+2}:
            g=[max(0,x) for x in tail(V,u,alpha)];assert all(g[n]<=g[n-1] for n in range(1,len(g)));ct['sharp_degree_boundary_contexts']+=1
        if u>=2:
            V=[2*u]
            if u>=3:V=[3,2*u]
            for alpha in {1,2,u+1,4*u+2}:
                g=[max(0,x) for x in tail(V,u,alpha)];assert all(g[n]<=g[n-1] for n in range(1,len(g)));ct['sharp_capacity_boundary_contexts']+=1
    out=dict(status='EXACT_QA_PASS_AUTOMATIC_LATE_C_CONES_AND_COMPLETE_U8_ENTRANCE',counts=dict(ct),
        complete_u8_profiles=profiles,complete_u8_contexts=contexts,integer_margins=sorted(cert),infinite_edge=infinite_edge,
        state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='Finite QA and ONE infinite-tail edge for the SOLE u8 residual profile. ALL finite paddings use proved initial-ones relative-density order. Improved degree cone h>=3u-1 groups the final two binary rows. Weight32 prior theorem is a logical input. Full independent reconstruction/formal audit pending. No earlier C/A2/original UI conclusion.')
    (ROOT/'audit_automatic_late_C_cones.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['complete_u8_contexts','integer_margins']}),flush=True)
    print(json.dumps(dict(hosts=len(contexts),integer_margins=len(cert))),flush=True)

if __name__=='__main__':main()
