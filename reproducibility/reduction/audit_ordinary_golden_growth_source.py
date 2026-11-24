"""Exact all-regime QA of a written universal growth theorem; no finite premise."""
from pathlib import Path
import sys,json,hashlib,time
from random import Random
from collections import Counter
from itertools import accumulate
from math import comb
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'audit_joint_structure.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_degree_boundary_CI_entrance import ci
from audit_joint_structure import fastconv
from audit_homogeneous_reference_and_sharp_entrance import rebuild
from audit_arbitrary_Fibonacci_tail_late_C import sign,add,sub,mul,power,evaluate
Q=(-1,1);PSI=(1,-1);PHI=(0,1);ZERO=(0,0);ONE=(1,0)

def main():
    start=time.monotonic();rng=Random(20261031165);ct=Counter();sha=hashlib.sha256();regimes=Counter()
    profiles=[]
    for r in range(1,8):
        for t in range(3,15):
            V=[t]*r;h=(t-1)*r
            for u in {0,max(0,h-2),h-1,h,h+1,2*h}:profiles.append((u,V))
    for _ in range(620):
        V=sorted(rng.choices(range(3,35),k=rng.randint(1,14)));h=sum(t-1 for t in V)
        profiles.append((rng.randint(0,2*h),V))
    for u,V in profiles:
        r=len(V);h=sum(t-1 for t in V);W=h+r;w=u+r;T=max(W,w+2);degree=u+h
        E=fastconv(ci(V),[comb(u,j) for j in range(u+1)])
        assert len(E)==degree+1 and all(x>=1 for x in E) and sum(E)>=3
        rho=ONE
        for t in V:
            b=mul(Q,sub(ONE,power(PSI,t)))
            assert sign(b)>0 and sign(sub(mul((2,0),power(Q,2)),b))>=0 and sign(sub(ONE,b))>0
            rho=mul(rho,b);ct['interval_factor_spectral_bounds']+=1
        assert sign(rho)>0 and sign(sub(ONE,rho))>0
        c=mul(power(PSI,u),evaluate(ci(V),(0,-1)))
        expected=mul(c,power(Q,h-u)) if h>=u else mul(c,power(PHI,u-h))
        if (h-u)%2:expected=(-expected[0],-expected[1])
        assert expected==rho;ct['spectral_normalization_identities']+=1
        Nmax=max(T+7,w+2+degree+4)
        Inf=arm_prefix(Nmax+1,[2]*u+V,Nmax);R=rebuild(V,Nmax)
        fib=[1,1]
        for i in range(2,Nmax+3):fib.append(fib[-1]+fib[-2])
        K=[];f=ZERO;U=ZERO
        for s in range(Nmax-w-1):
            K.append(ONE if not s else sub(ONE,mul(Q,K[-1])))
            assert sign(sub(K[-1],power(Q,2)))>=0 and sign(sub(ONE,K[-1]))>=0
            f=sub((E[s] if s<=degree else 0,0),mul(Q,f));U=add(U,f)
            assert sign(sub(U,ONE))>=0;ct['positive_kernel_prefix_mass_bounds']+=1
            N=w+2+s
            loss=sum(E[i]*(fib[s-i+2]-1) for i in range(min(s,degree)+1))
            assert Inf[N]==R[N]-loss;ct['infinite_initial_fixed_binary_model_identities']+=1
            if N>=T:
                actual=(-Inf[N],Inf[N-1]);spectral=mul(rho,power(PSI,N-W));predicted=sub(U,spectral)
                assert actual==predicted,(u,V,N,actual,predicted)
                lower=sub(ONE,mul(rho,power(Q,N-W)))
                assert sign(sub(actual,lower))>=0 and sign(lower)>0
                ct['exact_golden_gap_identities']+=1
                if s>degree:ct['golden_gap_reads_beyond_entire_CI_support']+=1
        for alpha in {1,2,3,max(1,h-u+1),rng.randint(1,h+u+10)}:
            Nend=alpha+2*u+W+1
            F=arm_prefix(alpha,[2]*u+V,Nend);I=arm_prefix(Nend+1,[2]*u+V,Nend);M=F.index(max(F))
            for n in range(1,M+1):
                assert F[n]*I[n-1]<=F[n-1]*I[n];ct['finite_ordinary_cumulative_density_edges']+=1
            for N in range(T,len(F)):
                if F[N-1]:assert sign((-F[N],F[N-1]))>0
                else:assert F[N]==0
                src=2*F[N-1]-F[N]
                assert sign(sub((src,0),mul(power(Q,2),(F[N-1],0))))>=0
                ct['all_padding_ordinary_golden_tail_edges']+=1
                ct['actual_late_source_relative_payments']+=1
                if h>u and N>=W+1 and F[N]>=F[N-1]>=F[N-2]:
                    d0=F[N-1]-F[N-2];d1=F[N]-F[N-1]
                    if d0:
                        assert sign(sub((2*d0-d1,0),mul(power(Q,2),(d0,0))))>0
                        ct['both_rising_late_source_increment_relative_payments']+=1
            regimes['above_crossing' if h>u else 'at_or_below_crossing']+=1;ct['actual_hosts']+=1
        sha.update(json.dumps([u,V,T,rho,Inf[T-1:T+2]],separators=(',',':')).encode());ct['CI_profiles']+=1
    controls=[]
    for alpha,u,V,N in [(2,3,[3,3],6),(3,2,[3,3],5),(10,5,[3,3],8)]:
        F=arm_prefix(alpha,[2]*u+V,N);assert sign((-F[N],F[N-1]))<0
        controls.append(dict(alpha=alpha,u=u,V=V,N=N,pair=F[N-1:N+1]))
    out=dict(status='EXACT_QA_UNIVERSAL_ORDINARY_GOLDEN_GROWTH_UNDER_AUDIT',counts=dict(ct),regimes=dict(regimes),sharp_prior_edge_controls=controls,state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        theorem='ALLu/h,ALLactualCIcapacities/counts/paddings: ordinaryF_N<phiFprev atN>=max(W,u+r+2) ifFprev>0, zerootherwise. Infinite-initial-padding gap EXACTLY positive E-kernel coefficient minus decaying normalized CI conjugate atom, atEVERYtailread including beyond entireCI support. Actual same-word finite-padding cumulative density used only through ordinary mode. Source E_N>=q^2Fprev; signed source increment identity only in stated nonnegative ordinary-slope branch. No finite premise. General ordinaryLC/C/A2/originalUI OPEN.')
    (ROOT/'audit_ordinary_golden_growth_source.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out),flush=True)

if __name__=='__main__':main()
