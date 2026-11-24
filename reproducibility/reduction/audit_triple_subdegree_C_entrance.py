"""Exact all-parameter-identity QA for the new h=u+3 late-C entrance; no finite premise."""
from pathlib import Path
from random import Random
from collections import Counter
from itertools import accumulate
import json,hashlib,time
from audit_degree_boundary_CI_entrance import partitions,ci
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import rebuild,c_minimum
from audit_arbitrary_Fibonacci_tail_late_C import sign,sub,mul
ROOT=Path(__file__).resolve().parent

def main():
    rng=Random(202610291211);ct=Counter();sha=hashlib.sha256();start=time.monotonic();contexts=[]
    for h in range(4,17):
        for ds in partitions(h):contexts.append((h-3,[d+1 for d in ds]))
    for _ in range(900):
        V=sorted(rng.choices(range(3,31),k=rng.randint(1,10)));u=sum(t-1 for t in V)-3
        if u>=0:contexts.append((u,V))
    for u,V in contexts:
        r=len(V);h=u+3;W=h+r;w=u+r;R=rebuild(V,W+2);rd=[1]+[R[n]-R[n-1] for n in range(1,len(R))]
        x,y=rd[W],rd[W+1];A=x*x+x*y-y*y
        assert R[W-2]==x-1 and R[W-1]==y and R[W]==x+y
        assert y>=x and sign(sub(mul((0,1),(x,0)),(y,0)))>0 and A>0
        E2=w*(w-1)//2+r
        for alpha in {1,2,3,4,5,rng.randint(6,max(6,u+h)),u+h+2}:
            F=arm_prefix(alpha,[2]*u+V,alpha+2*u+W+3);G=list(accumulate(F));D=[1]+[max(0,F[n]-F[n-1]) for n in range(1,len(F))]
            raw=[1]+[F[n]-F[n-1] for n in range(1,len(F))]
            if alpha==1:a,b,c=2,2*w+1,2*E2+w+2
            elif alpha==2:a,b,c=1,w+2,E2+2*w+2
            elif alpha==3:a,b,c=1,w+1,E2+w+3
            else:a,b,c=1,w+1,E2+w+2
            assert [rd[W-1]-raw[W-1],rd[W]-raw[W],rd[W+1]-raw[W+1]]==[a,b,c]
            assert F[W-2]==x-1 and F[W-1]==y-a and F[W]==x+y-a-b
            P=(y-a)*(x-b)-(x-1)*(y-c);Q=(x+y-a-b)*(x-b)-(y-a)*(y-c)
            assert P==x*(c-a)-y*(b-1)+a*b-c
            assert Q==A-x*(a+2*b)+y*(a-b+c)+b*b+a*b-a*c
            if w>=6:
                assert b>=2*a and c>=3*b and P>=2 and Q>0
                assert sign(sub(mul((0,1),(x-b,0)),(y-c,0)))>0
                ct['unbounded_three_loss_and_two_seed_identity_instances']+=1
            if D[W+1]>D[W]>0:
                for k in range(1,W+1):assert G[k]*D[W]>=G[k-1]*D[W+1];ct['all_prefix_strong_cumulative_seed_products']+=1
                ct['strictly_growing_boundary_hosts']+=1
            c_minimum(F,D,W+1,len(F)-1,ct,literal=len(V)<=2 and u<=25)
            ct['actual_hosts']+=1
        sha.update(json.dumps([u,V,x,y,A],separators=(',',':')).encode());ct['CI_profiles']+=1
    out=dict(status='EXACT_QA_TRIPLE_SUBDEGREE_ACTUAL_LATE_C_UNDER_AUDIT',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='Proposed UNBOUNDED h=u+3 actual late-C theorem. Every finite range/random word here is QA ONLY; NO NEW finite entrance premise. Actual losses retain BOTH finite binary and initial-one sources and the reference numerator unit at W-2. Universal late-D-LC is an already proved dependency. Earlier C/A2/original UI OPEN.')
    (ROOT/'audit_triple_subdegree_C_entrance.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)

if __name__=='__main__':main()
