"""Exact finite QA of the unbounded 4w+30>=13delta all-padding C proof."""
from pathlib import Path
import sys,json,time,hashlib
from math import comb,prod
from random import Random
from itertools import accumulate
from collections import Counter
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import rebuild,c_minimum
from audit_degree_boundary_CI_entrance import ci
from audit_joint_structure import fastconv
from audit_arbitrary_Fibonacci_tail_late_C import sign,sub,add,mul,power
Q=(-1,1);PHI=(0,1);ONE=(1,0);ZERO=(0,0)
def v(A,j):return A[j] if 0<=j<len(A) else 0
def cdf(A,j):return A[j] if 0<=j<len(A) else (0 if j<0 else A[-1])

def main():
    start=time.monotonic();rng=Random(20261031225);ct=Counter();sha=hashlib.sha256();profiles=[]
    for delta in range(5,61):
        for r in range(2,11):
            w=max((13*delta-30+3)//4,33-delta);u=w-r;h=u+delta
            if u<0 or h<2*r:continue
            for balance in (False,True):
                ds=[2]*r
                for k in range(h-2*r):ds[k%r if balance else -1]+=1
                profiles.append((u,sorted(d+1 for d in ds)))
    for _ in range(200):
        V=sorted(rng.choices(range(3,26),k=rng.randint(2,12)));h=sum(t-1 for t in V)
        maxdelta=(4*(h+len(V))+30)//17
        if maxdelta>=5:
            delta=rng.randint(5,maxdelta);u=h-delta
            if sum(V)>=33:profiles.append((u,V))
    for u,V in profiles:
        r=len(V);h=sum(t-1 for t in V);W=h+r;w=u+r;delta=h-u;n=delta-2
        assert W>=33 and 4*w+30>=13*delta and h<=3*u+2 and 4*w+4>=13*n and 8*(w-n)>=15*(n+1)
        E=fastconv(ci(V),[comb(u,j) for j in range(u+1)]);S_E=list(accumulate(E));En,Ep=E[n],E[n-1]
        for j in range(1,n+1):assert 4*E[j]>=9*E[j-1];ct['nine_quarters_CI_head_ratios']+=1
        assert 8*E[n+1]>=15*En;ct['fifteen_eighths_next_CI_ratio']+=1
        I=arm_prefix(W+3,[2]*u+V,W+1);R=rebuild(V,W+1);Gref=list(accumulate(R));rd=[0,0]+[R[j]-R[j-1] for j in range(2,len(R))]
        x,y=rd[W:W+2];M=1
        for t in V:M=t*M-1
        assert 5*M<=2*x and x>=2*prod(V)>=2*(W+3)>=40
        assert 20*rd[W-1]<=13*x and 5*Gref[W-4]>=3*x and 5*Gref[W-3]>=6*x
        ct['refined_reference_mass_and_TWO_read_budgets']+=1
        rho=ONE
        for t in V:rho=mul(rho,mul(Q,sub(ONE,power((1,-1),t))))
        f=[];cur=ZERO
        for j in range(n+2):cur=sub((E[j],0),mul(Q,cur));f.append(cur)
        Un=add(mul(Q,(S_E[n],0)),mul(power(Q,2),f[n]))
        Up=add(mul(Q,(S_E[n-1],0)),mul(power(Q,2),f[n-1]))
        assert (-I[W],I[W-1])==sub(Un,rho)
        assert (-I[W-1],I[W-2])==sub(add(Up,mul(PHI,rho)),PHI)
        ct['exact_current_AND_previous_ordinary_golden_kernel_identities']+=2
        for alpha in range(1,delta+2):
            A=[I[N]-cdf(S_E,N-alpha-w-1) for N in range(W-2,W+2)]
            F0,F1,F2,F3=A;a,b=F2-F1,F3-F2;g=(-b,a);ec=(-F2,F1);ep=(-F1,F0)
            assert sign(sub(mul((8,0),(-a,F1-F0)),(13*Ep,0)))>=0
            ct['ALL_padding_current_W_thirteen_eighths_golden_bounds']+=1
            assert sign(sub(mul((4,0),g),(5*En,0)))>=0
            if alpha==1:
                assert sign(sub(mul((2,0),g),(3*En,0)))>=0
                assert sign(sub((2*En,0),ec))>=0 and sign(sub((2*Ep,0),ep))>=0
            elif alpha==2:
                assert sign(sub(mul((8,0),g),(10*En+5*Ep,0)))>=0
                assert sign(sub((35*En,0),mul((18,0),ec)))>=0 and sign(sub((35*Ep,0),mul((18,0),ep)))>=0
            else:
                assert sign(sub((35*En,0),mul((18,0),ec)))>=0 and sign(sub((275*Ep,0),mul((162,0),ep)))>=0
            if b>a>0:
                assert F1-F0<=a and sign((-F2,F1))>0
                assert a*F2-b*F1>0 and a*F1-b*F0>0
                ct['ALL_padding_BOTH_ordinary_seed_determinants']+=2
            ct['ALL_padding_next_gap_and_ordinary_gap_upper_bounds']+=1
        fib=[1,1]
        while len(fib)<=n:fib.append(fib[-1]+fib[-2])
        for alpha in {1,2,3,delta+1}:
            F=arm_prefix(alpha,[2]*u+V,alpha+2*u+W+1);G=list(accumulate(F));D=[0,0]+[max(0,F[j]-F[j-1]) for j in range(2,len(F))]
            a,b=D[W:W+2]
            loss=[sum(E[i]*fib[j-i] for i in range(j+1))+v(E,j-alpha+1) for j in range(n+1)];S=list(accumulate(loss));T=list(accumulate(S))
            for j in range(n-1):
                k=w+2+j;distance=W+1-k;assert distance>=3
                assert 29*S[j]<=198*E[j] and G[k]==Gref[k]-T[j]
                if b>a>0:
                    assert 40*En*Gref[k-1]>=243*a*E[j]
                    assert G[k]*a-G[k-1]*b>0
                    ct['ALL_distance_current_W_plus_one_C_source_payments']+=1
            if b>a>0:
                assert a*F[W]-b*F[W-1]>0 and a*F[W-1]-b*F[W-2]>0
                for k in range(1,W+1):assert G[k]*a>=G[k-1]*b;ct['ALL_prefix_STRONG_C_entrance_products']+=1
            c_minimum(F,D,W,len(F)-1,ct)
            ct['actual_hosts']+=1
        ct['profiles_outside_OLD_sharp_wedge']+=4*w+17<13*delta
        sha.update(json.dumps([u,V,n,x,M],separators=(',',':')).encode());ct['CI_profiles']+=1
    out=dict(status='EXACT_QA_WEAKER_COUNT_WEDGE_ENTIRE_C_ENTRANCE_UNDER_AUDIT',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='Candidate whole-wedge improvement4w+30>=13delta (equiv17u+4r+30>=13h),EVERYactualC fromN>=W. ALLpadding two ordinary seeds +allGprefix strongentrance atW+1 are paid by CORRECT finite-padding source sign,new mass2/5,and15/8next-ratio. Oldweight32handlesW<=32. Ifaudited,uniformu>=h-9CfromW andu>=h-5CfromW-1. General earlierC/fullA2/originalUI OPEN;finiteQAONLY.')
    (ROOT/'audit_weaker_count_wedge_C_entrance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)

if __name__=='__main__':main()
