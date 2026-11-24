"""Exact QA of unbounded reference and actual W-1 proofs; no sampled theorem premise."""
from pathlib import Path
import sys,json,random,time,hashlib
from itertools import accumulate
from math import comb
from collections import Counter
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import rebuild
from audit_arbitrary_Fibonacci_tail_late_C import sign,sub,add,mul,power
from audit_degree_boundary_CI_entrance import ci
from audit_joint_structure import fastconv
from audit_binary_CI_infinite_padding_entrance import binary
Q=(-1,1);P=(0,1);PSI=(1,-1);ONE=(1,0);ZERO=(0,0)

def main():
    rng=random.Random(20261031212);ct=Counter();sha=hashlib.sha256();start=time.monotonic();bad=[];profiles=[]
    for t in range(3,36):
        for r in range(1,7):
            V=[t]*r;h=(t-1)*r
            for u in {0,max(0,h-5),h-3,h-2,h-1,h,h+2}:profiles.append((u,V))
    for a in range(3,22):
        for b in range(a,28):
            V=[3,a,b];h=sum(t-1 for t in V)
            profiles.append((max(0,h-3),V))
    for _ in range(650):
        V=sorted(rng.choices(range(3,29),k=rng.randint(1,10)));h=sum(t-1 for t in V);profiles.append((rng.randint(0,2*h),V))
    for u,V in profiles:
        r=len(V);h=sum(t-1 for t in V);W=h+r;w=u+r;delta=h-u;N=W-1
        if N<3:continue
        rho=ONE
        for t in V:rho=mul(rho,mul(Q,sub(ONE,power(PSI,t))))
        b1=r-int(V[0]==3);R=rebuild(V,W);RG=list(accumulate(R));RD=[0,0]+[R[i]-R[i-1] for i in range(2,len(R))]
        rgap=add(sub(mul((b1,0),P),power(P,3)),mul(power(P,3),rho))
        assert rgap==(-RD[N],RD[N-1]);ct['previous_reference_boundary_exact_identities']+=1
        rexception=(r==2 and V[0]==3) or V in ([3,4,4],[3,4,6])
        if r>=2:assert (sign(rgap)<=0)==rexception
        for k in range(1,N-2):
            assert RG[k]*RD[N-1]>=RG[k-1]*RD[N];ct['complete_reference_W_minus_one_C_reads']+=1
        if r==2 and V[0]==3:
            T=V[1];fib=[0,1]
            while len(fib)<=T+2:fib.append(fib[-1]+fib[-2])
            a,b=RD[N-1],RD[N];assert a==2*fib[T]-1 and b==2*fib[T+1]-1
            envelope=(fib[T+2]-1)*a-(fib[T+1]-1)*b
            assert envelope==fib[T-3]+2*(-1)**(T+1)
            assert (envelope<0)==(T==4);ct['unbounded_two_factor_binary_envelope_formula_QA']+=1
        I=arm_prefix(W+2,[2]*u+V,W);ia=I[N-1]-I[N-2];ib=I[N]-I[N-1]
        if r>=2 and delta>=3:
            E=fastconv(ci(V),[comb(u,j) for j in range(u+1)]);s=delta-3;f=ZERO
            for j in range(s+1):f=sub((E[j],0),mul(Q,f))
            assert (-ib,ia)==add(rgap,f) and sign((-ib,ia))>0
            C=fastconv(ci(V),binary(u-1)) if u else [0]
            cv=lambda j:C[j] if 0<=j<len(C) else 0
            assert ia==cv(h-4)+r*(r+1)//2-int(V[0]==3) and ib==cv(h-3)+r
            ct['exact_second_previous_CI_bonus_identities']+=1
            if not u:assert ia>=ib
            elif h<=3*u+5:
                assert sign(sub(f,ONE))>=0
                if s:assert E[s]>=w>=3 and sign(sub(f,mul(power(Q,2),(E[s],0))))>=0
                if b1==1:
                    assert sign(sub(rho,power(Q,2)))>0 and sign(sub(mul(power(P,3),rho),P))>0
                elif b1==2:assert sub(mul((b1,0),P),power(P,3))==(-1,0)
                else:assert sign(sub(mul((b1,0),P),power(P,3)))>0
                ct['complete_actual_monotone_head_payment_checks']+=1
            else:
                assert cv(h-4)>=cv(h-3) and ia>=ib
                ct['complementary_actual_symmetric_row_payment_checks']+=1
            ct['actual_infinite_padding_previous_boundary_golden_edges']+=1
        for alpha in {1,2,max(1,delta+1)}:
            F=arm_prefix(alpha,[2]*u+V,alpha+2*u+W+1);G=list(accumulate(F));D=[0,0]+[max(0,F[i]-F[i-1]) for i in range(2,len(F))]
            if r>=2 and delta>=3:
                assert D[N]*ia<=D[N-1]*ib
                if D[N-1]:assert sign((-D[N],D[N-1]))>0
                else:assert D[N]==0
                ct['all_padding_previous_boundary_golden_edges']+=1
            if delta<=2:assert F[:N+1]==R[:N+1]
            for k in range(1,min(N-3,w+1)+1):
                assert G[k]*D[N-1]>=G[k-1]*D[N];ct['actual_previous_boundary_large_shift_C_reads']+=1
            if u>=h-5:
                for k in range(1,N-2):assert G[k]*D[N-1]>=G[k-1]*D[N];ct['five_gap_ALLshift_previous_boundary_C_reads']+=1
            ct['actual_hosts']+=1
        sha.update(json.dumps([u,V,rgap,ia,ib],separators=(',',':')).encode());ct['profiles']+=1
    for T in range(3,601):
        fib=[0,1]
        while len(fib)<=T+2:fib.append(fib[-1]+fib[-2])
        a,b=2*fib[T]-1,2*fib[T+1]-1
        z=(fib[T+2]-1)*a-(fib[T+1]-1)*b
        assert z==fib[T-3]+2*(-1)**(T+1) and (z<0)==(T==4)
        ct['complete_range_Cassini_formula_QA']+=1
    lower=mul(Q,sub(ONE,power(Q,4)))
    for t in range(3,351):
        fact=mul(Q,sub(ONE,power(PSI,t)))
        assert sign(sub(fact,lower))>=0
        ct['all_capacity_lower_norm_QA']+=1
    ordered=[[3,4,4],[3,4,6],[3,6,4],[3,4]]
    for _ in range(350):ordered.append(rng.choices(range(3,23),k=rng.randint(2,9)))
    for V in ordered:
        W=sum(V);N=W-1;R=rebuild(V,W);G=list(accumulate(R));D=[0,0]+[R[i]-R[i-1] for i in range(2,len(R))]
        rho=ONE
        for t in V:rho=mul(rho,mul(Q,sub(ONE,power(PSI,t))))
        b1=len(V)-int(V[0]==3)
        assert (-D[N],D[N-1])==add(sub(mul((b1,0),P),power(P,3)),mul(power(P,3),rho))
        for k in range(1,N-2):assert G[k]*D[N-1]>=G[k-1]*D[N];ct['arbitrary_order_reference_C_boundary_reads']+=1
        ct['arbitrary_order_reference_profiles']+=1
    for delta in range(1,9):
        for w in range(151):
            if 4*w+17<13*delta:assert w+delta<=29
            ct['eight_gap_old_wedge_split_QA']+=1
    out=dict(status='EXACT_QA_PREVIOUS_BOUNDARY_REFERENCE_AND_ACTUAL_C_UNDER_AUDIT',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='Written unbounded proof under independent audit: reference ALLC fromW-1; actual CURRENTW-1 allR>=max(3,h-u-2),henceALLshiftswhen u>=h-5. Existing MASTER1211 gives allactualC fromW foru>=h-4, so this would give halflinefromW-1 in that OLDcountfamily. General earlierC,A2,originalUI OPEN; u=h-5 still has currentW gap unless separately paid. FOUR constant reference exceptions are directly Lean kernel-reconstructed,all other finite checks QA ONLY. The old wedge plus weight32 ALREADY gives allu>=h-8 lateC fromW+1.')
    (ROOT/'audit_previous_boundary_C.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)

if __name__=='__main__':main()
