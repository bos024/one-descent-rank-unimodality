"""Exact QA of the UNBOUNDED factor-count late-C wedge, not a finite theorem premise."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'audit_joint_structure.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from random import Random
from math import comb,prod
from collections import Counter
from itertools import accumulate
import json,hashlib,time
from audit_degree_boundary_CI_entrance import ci
from audit_joint_structure import fastconv
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import rebuild,c_minimum
from audit_arbitrary_Fibonacci_tail_late_C import sign,sub,mul,power,numerator_append

def main():
    rng=Random(20261031121);ct=Counter();sha=hashlib.sha256();start=time.monotonic();contexts=[]
    for delta in range(5,25):
        for r in range(1,9):
            w=(13*delta-17+3)//4;u=w-r;h=u+delta
            if u<0 or h<2*r:continue
            for balanced in (False,True):
                ds=[2]*r
                if balanced:
                    for k in range(h-2*r):ds[k%r]+=1
                else:ds[-1]+=h-2*r
                contexts.append((u,[d+1 for d in sorted(ds)]))
    for t in range(3,181):
        z=sub(power((0,1),t+1),(0,1))
        assert sign(sub(mul((7**t,0),z),(t*8**t,0)))>=0;ct['all_capacity_amplification_exact_QA']+=1
    for delta in range(5,15):
        for r in range(1,7):
            for shift in (0,1,5):
                V=sorted([3+((i+3)*(delta+shift)+i*i)%12 for i in range(r)])
                h=sum(t-1 for t in V);u=h-delta
                if u>=0 and 4*(u+r)+17>=13*delta:contexts.append((u,V))
    for _ in range(1000):
        V=sorted(rng.choices(range(3,26),k=rng.randint(1,14)));h=sum(t-1 for t in V);maxdelta=(4*(h+len(V))+17)//17
        if maxdelta<5:continue
        delta=rng.randint(5,maxdelta);u=h-delta
        if u>=0:contexts.append((u,V))
    for u,V in contexts:
        r=len(V);h=sum(t-1 for t in V);delta=h-u;w=u+r;W=h+r;p=delta-2;N0=w+2
        assert 4*w+17>=13*delta and N0==W-p
        R=rebuild(V,W+2);g=list(accumulate(R));rd=[1]+[R[n]-R[n-1] for n in range(1,len(R))];x,y=rd[W],rd[W+1];A=x*x+x*y-y*y
        assert x>=2 and 5*y>=8*x and A>0 and R[W-2]==x-1 and R[W-1]==y and R[W]==x+y
        num=[1]
        for t in V:num=numerator_append(num,t)
        M=sum(num);assert 0<M<prod(V) and 2*M<=x
        assert g[W-2]==x+y-M and g[W-1]==x+2*y-M
        assert g[W-2]>=2*x and 2*g[W-1]>=7*x
        ct['exact_reference_numerator_mass_and_CDF_resources']+=1
        for n in range(1,len(g)):assert g[n]<=2*g[n-1];ct['reference_CDF_dyadic_growth_comparisons']+=1
        E=fastconv(ci(V),[comb(u,n) for n in range(u+1)])
        fib=[1,1]
        for n in range(2,p+2):fib.append(fib[-1]+fib[-2])
        for alpha in {1,2,3,delta,delta+1,u+h+2}:
            loss=[sum(E[i]*fib[j-i] for i in range(j+1))+(E[j-alpha+1] if j>=alpha-1 else 0) for j in range(p+2)]
            for j in range(1,len(loss)):
                assert j*loss[j]>=(w-j+1)*loss[j-1] and 4*loss[j]>=9*loss[j-1];ct['actual_loss_nine_quarters_growth_comparisons']+=1
            a=sum(loss[:p]);b,c=loss[p:p+2];assert a<=b and 4*c>=9*b
            F=arm_prefix(alpha,[2]*u+V,alpha+2*u+W+3);G=list(accumulate(F));raw=[1]+[F[n]-F[n-1] for n in range(1,len(F))];D=[max(0,z) for z in raw]
            assert [rd[N0+j]-raw[N0+j] for j in range(p+2)]==loss
            assert F[W-1]==y-a and F[W]==x+y-a-b
            if D[W+1]>D[W]>0:
                D0,D1=D[W],D[W+1]
                gap=sub(mul((0,1),(D0,0)),(D1,0));assert sign(sub(mul((8*x,0),gap),(5*b*D0,0)))>0
                S=0;T=0
                for j in range(p+1):
                    prevT=T;S+=loss[j];T+=S;k=N0+j;d=W-k
                    resource=g[k]*D0-g[k-1]*D1;source=T*D0-prevT*D1
                    if d:
                        assert 8*2**d*resource>20*b*D0 and 2**d*source<=2*b*D0
                    else:assert 16*resource>35*b*D0 and source<=2*b*D0
                    assert G[k]*D0-G[k-1]*D1==resource-source>0
                    ct['exact_integer_sharp_dyadic_prefix_payments']+=1
                assert 20*(F[W]*D0-F[W-1]*D1)>=20*A+7*b*b;ct['actual_ordinary_boundary_seed_payments']+=1
                for k in range(1,W+1):assert G[k]*D0>=G[k-1]*D1;ct['all_prefix_strong_C_seed_products']+=1
                ct['strictly_growing_actual_boundary_hosts']+=1
            c_minimum(F,D,W+1,len(F)-1,ct,literal=r<=2 and delta<=8)
            ct['actual_hosts']+=1
        sha.update(json.dumps([u,V,delta,x,y,A],separators=(',',':')).encode());ct['CI_profiles']+=1;ct['profiles_beyond_previous_wedge']+=w<4*delta-5
    out=dict(status='EXACT_QA_SHARP_ACTUAL_CI_COUNT_WEDGE_UNDER_AUDIT',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='WHOLE unbounded sharper cone 4(u+r)+17>=13(h-u),delta>=5 proposed actual late C. Every finite profile and bound here is QA ONLY, NO finite entrance premise. Reference numerator MASS and stronger homogeneous ratio reduce the required source growth to9/4; complete source cumulatives and ordinary seed margin retained. General earlier C/A2/original UI OPEN.')
    (ROOT/'audit_sharp_CI_count_wedge.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)

if __name__=='__main__':main()
