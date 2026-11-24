"""Exact finite QA of the surplus ordinary-tail LC proof and all its source atoms."""
from pathlib import Path
import sys,json,time,hashlib
from math import comb,prod
from itertools import accumulate
from collections import Counter
from random import Random
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import rebuild
from audit_degree_boundary_CI_entrance import ci
from audit_joint_structure import fastconv
from audit_arbitrary_Fibonacci_tail_late_C import sign,add,sub,mul,power,evaluate
Q=(-1,1);PSI=(1,-1);ONE=(1,0);ZERO=(0,0)
def main():
    start=time.monotonic();rng=Random(20261031403);ct=Counter();sha=hashlib.sha256()
    profiles=[]
    for r in range(1,6):
        for t in range(3,17):
            V=[t]*r;h=(t-1)*r
            for u in {max(16,h),max(16,h+1),max(16,2*h)}:profiles.append((u,V))
    for _ in range(130):
        V=sorted(rng.choices(range(3,30),k=rng.randint(1,9)));h=sum(t-1 for t in V)
        profiles.append((rng.randint(max(h,16),max(16,2*h)),V))
    for u,V in profiles:
        h=sum(t-1 for t in V);r=len(V);W=h+r;w=u+r;L=ci(V)
        E=fastconv(L,[comb(u,j) for j in range(u+1)]);d=len(E)-1;CE=list(accumulate(E))
        c=mul(power(PSI,u),evaluate(L,(0,-1)));assert sign(sub(ONE,c))>0 and sign(add(ONE,c))>0
        J=[];f=ZERO
        for j in range(d):
            f=sub((E[j],0),mul(Q,f));J.append(sub(f,mul(c,power(PSI,j))))
        for j in range(d+1):
            rhs=add(J[j] if j<d else ZERO,mul(Q,J[j-1]) if j else ZERO)
            assert rhs==((E[j]-c[0],-c[1]) if j==0 else (E[j],0))
            ct['exact_entire_quotient_source_identity_coefficients']+=1
        B=[];cur=mul(Q,c)
        for j in range(d):cur=add(cur,J[j]);B.append(cur)
        for j in range(d):
            assert sign(B[j])>0 and sign(J[j])>0
            if j:assert sign(sub(B[j],B[j-1]))>=0
            if 0<j<d-1:assert sign(sub(mul(B[j],B[j]),mul(B[j-1],B[j+1])))>=0
            ct['entire_positive_cumulative_quotient_LC_reads']+=1
        assert sign(sub(mul(B[1],J[1]),mul(B[0],J[2])))>0
        Tmax=w+2+d+3;I=arm_prefix(Tmax+1,[2]*u+V,Tmax)
        for s in range(d+3):
            bs=B[s] if s<d else B[-1];bp=B[s-1] if 0<=s-1<d else (ZERO if s==0 else B[-1])
            assert (-I[w+2+s],I[w+1+s])==bs
            rhs=add(bs,mul(Q,bp))
            if s==0:rhs=add(rhs,mul(power(Q,2),c))
            assert rhs==(CE[s] if s<len(CE) else CE[-1],0)
            ct['exact_cumulative_source_and_infinite_ordinary_deficit_coefficients']+=1
        R=rebuild(V,w+2);x=R[W]-R[W-1];y=R[W+1]-R[W];A=x*x+x*y-y*y
        assert 0<A<=R[W]<=R[w];ct['all_capacity_reference_first_boundary_budgets']+=1
        for alpha in {1,2,3,max(4,d//2),d+2}:
            F=arm_prefix(alpha,[2]*u+V,alpha+2*u+W+1);M=F.index(max(F))
            for n in range(w+1,len(F)-1):
                assert F[n]**2>=F[n-1]*F[n+1];ct['actual_entire_ordinary_LC_tail_centres']+=1
            assert F[w+1]==R[w+1] and F[w+2]<R[w+2]
            for s in range(-1,d+3):
                N=w+2+s;idx=s-alpha+1
                loss=CE[idx] if 0<=idx<len(CE) else (0 if idx<0 else CE[-1])
                assert (F[N] if N<len(F) else 0)==I[N]-loss;ct['exact_ALL_padding_ordinary_model_reads']+=1
            ct['actual_hosts']+=1
        sha.update(json.dumps([u,V,c,J[:3],B[:3],A],separators=(',',':')).encode());ct['CI_profiles']+=1
    out=dict(status='EXACT_QA_SURPLUS_ORDINARY_FULL_TAIL_LC_UNDER_AUDIT',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
      scope='ALLu>=max(h,16) ENTIREordinaryFLCfromcentre u+r+1,writtenunboundedcumulativequotient/cut/startup proof. No relativeLC/CassiniA lowerbound claim; finiteQAONLY;original/generalC/A2OPEN.')
    (ROOT/'audit_surplus_ordinary_tail_LC.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()

