"""Exact QA: CI-count loss growth and ALL-padding h=u+4 actual C entrance."""
from pathlib import Path
from random import Random
from math import comb
from collections import Counter
from itertools import accumulate
import json,hashlib,time
from audit_degree_boundary_CI_entrance import partitions,ci
from audit_joint_structure import fastconv
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import rebuild,c_minimum
ROOT=Path(__file__).resolve().parent

def main():
    rng=Random(202610291231);ct=Counter();sha=hashlib.sha256();start=time.monotonic();contexts=[]
    for h in range(5,17):
        for ds in partitions(h):contexts.append((h-4,[d+1 for d in ds]))
    for _ in range(720):
        V=sorted(rng.choices(range(3,30),k=rng.randint(1,10)));u=sum(t-1 for t in V)-4
        if u>=0:contexts.append((u,V))
    for u,V in contexts:
        r=len(V);h=u+4;W=h+r;w=u+r;R=rebuild(V,W+2);rd=[1]+[R[n]-R[n-1] for n in range(1,len(R))]
        x,y=rd[W],rd[W+1];A=x*x+x*y-y*y
        assert R[W-3]<=y-x+1 and [R[W-2],R[W-1],R[W]]==[x-1,y,x+y] and A>0
        E=fastconv(ci(V),[comb(u,j) for j in range(u+1)])
        assert E[:4]==[1,w,w*(w-1)//2+r,comb(w,3)+r*w-V.count(3)]
        for j in range(1,len(E)):
            assert j*E[j]>=(w-j+1)*E[j-1];ct['actual_CI_factor_count_growth_margins']+=1
        for alpha in {1,2,3,4,5,6,u+h+2}:
            F=arm_prefix(alpha,[2]*u+V,alpha+2*u+W+3);G=list(accumulate(F));raw=[1]+[F[n]-F[n-1] for n in range(1,len(F))];D=[max(0,z) for z in raw]
            loss=[rd[W-2+j]-raw[W-2+j] for j in range(4)];a,l,b,c=loss;S=a+l;e=1+a
            EH=[0]*4
            fib=[1,1,2,3]
            for j in range(4):EH[j]=sum(E[i]*fib[j-i] for i in range(j+1))+(E[j-alpha+1] if j>=alpha-1 else 0)
            assert loss==EH
            assert F[W-3]==R[W-3] and F[W-2]==x-e and F[W-1]==y-S and F[W]==x+y-S-b
            if w>=11:
                assert 1<=a<=2 and S>=e and b>=2*S and b>=2*e+3 and c>=3*b and S<=2*w+3<=x and 2*y>=3*x
                P=F[W-1]*raw[W]-F[W-2]*raw[W+1]
                Q=F[W]*raw[W]-F[W-1]*raw[W+1]
                assert P>=2*e*e and Q>0
                if raw[W+1]>=0:assert F[W-2]*raw[W]-F[W-3]*raw[W+1]>0
                ct['unbounded_loss_and_three_seed_instances']+=1
            if D[W+1]>D[W]>0:
                for k in range(1,W+1):assert G[k]*D[W]>=G[k-1]*D[W+1];ct['all_prefix_strong_C_seed_comparisons']+=1
                ct['strictly_growing_boundary_hosts']+=1
            c_minimum(F,D,W+1,len(F)-1,ct,literal=r<=2 and u<=25)
            ct['actual_hosts']+=1
        sha.update(json.dumps([u,V,x,y,A,E[:4]],separators=(',',':')).encode());ct['CI_profiles']+=1
    out=dict(status='EXACT_QA_FOUR_SUBDEGREE_ACTUAL_LATE_C_UNDER_AUDIT',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='UNBOUNDED h=u+4 proposed actual late-C proof. All finite cases are QA ONLY; smallw<11 uses OLD weight32 theorem. Actual factor-count source growth uses w=u+r, includes all finite-count and one-padding losses and the reference numerator x-1. Original C/A2/UI OPEN.')
    (ROOT/'audit_four_subdegree_C_entrance.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)

if __name__=='__main__':main()
