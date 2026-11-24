"""Exact QA of the UNBOUNDED factor-count late-C wedge, not a finite theorem premise."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'audit_joint_structure.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from random import Random
from math import comb
from collections import Counter
from itertools import accumulate
import json,hashlib,time
from audit_degree_boundary_CI_entrance import ci
from audit_joint_structure import fastconv
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import rebuild,c_minimum
from audit_arbitrary_Fibonacci_tail_late_C import sign,sub,mul

def main():
    rng=Random(20261031101);ct=Counter();sha=hashlib.sha256();start=time.monotonic();contexts=[]
    for delta in range(5,15):
        for r in range(1,7):
            for shift in (0,1,5):
                V=sorted([3+((i+3)*(delta+shift)+i*i)%12 for i in range(r)])
                h=sum(t-1 for t in V);u=h-delta
                if u>=0 and u+r>=4*delta-5:contexts.append((u,V))
    for _ in range(1000):
        V=sorted(rng.choices(range(3,26),k=rng.randint(1,14)));h=sum(t-1 for t in V);maxdelta=(h+len(V)+5)//5
        if maxdelta<5:continue
        delta=rng.randint(5,maxdelta);u=h-delta
        if u>=0:contexts.append((u,V))
    for u,V in contexts:
        r=len(V);h=sum(t-1 for t in V);delta=h-u;w=u+r;W=h+r;p=delta-2;N0=w+2
        assert w>=4*delta-5 and N0==W-p
        R=rebuild(V,W+2);g=list(accumulate(R));rd=[1]+[R[n]-R[n-1] for n in range(1,len(R))];x,y=rd[W],rd[W+1];A=x*x+x*y-y*y
        assert x>=2 and 2*y>=3*x and A>0 and R[W-2]==x-1 and R[W-1]==y and R[W]==x+y
        for n in range(1,len(g)):assert g[n]<=2*g[n-1];ct['reference_CDF_dyadic_growth_comparisons']+=1
        E=fastconv(ci(V),[comb(u,n) for n in range(u+1)])
        fib=[1,1]
        for n in range(2,p+2):fib.append(fib[-1]+fib[-2])
        for alpha in {1,2,3,delta,delta+1,u+h+2}:
            loss=[sum(E[i]*fib[j-i] for i in range(j+1))+(E[j-alpha+1] if j>=alpha-1 else 0) for j in range(p+2)]
            for j in range(1,len(loss)):
                assert j*loss[j]>=(w-j+1)*loss[j-1] and loss[j]>=3*loss[j-1];ct['actual_loss_triple_growth_comparisons']+=1
            a=sum(loss[:p]);b,c=loss[p:p+2];assert 2*a<=b and c>=3*b
            F=arm_prefix(alpha,[2]*u+V,alpha+2*u+W+3);G=list(accumulate(F));raw=[1]+[F[n]-F[n-1] for n in range(1,len(F))];D=[max(0,z) for z in raw]
            assert [rd[N0+j]-raw[N0+j] for j in range(p+2)]==loss
            assert F[W-1]==y-a and F[W]==x+y-a-b
            if D[W+1]>D[W]>0:
                D0,D1=D[W],D[W+1]
                gap=sub(mul((0,1),(D0,0)),(D1,0));assert sign(sub(mul((x,0),gap),(b*D0,0)))>0
                S=0;T=0
                for j in range(p+1):
                    prevT=T;S+=loss[j];T+=S;k=N0+j;d=W-k
                    resource=g[k]*D0-g[k-1]*D1;source=T*D0-prevT*D1
                    if d:
                        assert 2**d*resource>b*D0 and 2*3**d*source<=3*b*D0
                        assert 3*2**d<=2*3**d
                    else:assert 2*resource>3*b*D0 and 2*source<=3*b*D0
                    assert G[k]*D0-G[k-1]*D1==resource-source>0
                    ct['exact_integer_dyadic_ternary_prefix_payments']+=1
                assert F[W]*D0-F[W-1]*D1>0;ct['actual_ordinary_boundary_seed_payments']+=1
                for k in range(1,W+1):assert G[k]*D0>=G[k-1]*D1;ct['all_prefix_strong_C_seed_products']+=1
                ct['strictly_growing_actual_boundary_hosts']+=1
            c_minimum(F,D,W+1,len(F)-1,ct,literal=r<=2 and delta<=8)
            ct['actual_hosts']+=1
        sha.update(json.dumps([u,V,delta,x,y,A],separators=(',',':')).encode());ct['CI_profiles']+=1
    out=dict(status='EXACT_QA_UNBOUNDED_CI_COUNT_WEDGE_LATE_C_UNDER_AUDIT',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='WHOLE unbounded cone u+r>=4(h-u)-5,delta>=5 proposed actual late C. Every finite profile and bound here is QA ONLY, NO finite entrance premise. Exact source pays EVERY cumulative read directly; ordinary and double cumulative losses retained. General earlier C/A2/original UI OPEN.')
    (ROOT/'audit_CI_count_wedge_late_C.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)

if __name__=='__main__':main()
