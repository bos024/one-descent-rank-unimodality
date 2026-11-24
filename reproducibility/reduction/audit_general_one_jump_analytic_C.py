"""Exact actual-word QA of the UNIFORM analytic one-jump C assembly."""
from pathlib import Path
from random import Random
from collections import Counter
from audit_minimum_staircase_scaled_dyadic import arm_prefix
import json,time
ROOT=Path(__file__).resolve().parent


def jump(F,L,N):return [1]+[sum(F[max(0,n-L):n]) for n in range(1,N+1)]


def main():
    start=time.monotonic();rng=Random(20261027128);counts=Counter()
    fib=[0,1]
    for n in range(1800):fib.append(fib[-1]+fib[-2])
    for case in range(3000):
        L=rng.randint(3,120)
        if case%4==0:h=L+2
        elif case%4==1:h=rng.randint(1,L+1)
        elif case%4==2:h=rng.randint(L+3,L+100)
        else:h=rng.randint(2,200)
        alpha=rng.choice([1,2,h+L,rng.randint(1,400)])
        N=2*h+L+1;F=arm_prefix(alpha,[2]*h,N+1);R=F.index(max(F))
        assert R<=2*h and F[2*h]-F[2*h-1]<=1
        delta1=2 if alpha==1 else 1
        delta2=2*h+3 if alpha==1 else h+3 if alpha==2 else h+2
        assert fib[h+3]-F[h+2]==delta1 and fib[h+4]-F[h+3]==delta2
        counts['exact_first_two_binary_defect_sets']+=1
        for n in range(h+2,R+1):
            assert (F[n]-1)**2>=F[n-1]*(F[n+1]-1)
            counts['actual_modified_binary_tail_minors']+=1
        A=jump(F,L,N)
        D=[0,0]+[max(0,A[n]-A[n-1]) for n in range(2,N+1)]
        ell=D.index(max(D));Rnew=max(n for n,x in enumerate(D) if x)
        assert ell<=R+1
        r=[0,0]+[fib[n]-(fib[n-L] if n>=L else 0) for n in range(2,N+1)]
        if h<=L+2:
            if h==L+2:assert ell<=2*h;counts['actual_diagonal_improved_mode_bounds']+=1
            for n in range(3,ell):
                assert D[n]**2*r[n-1]*r[n+1]>=D[n-1]*D[n+1]*r[n]**2
                counts['actual_UNIFORM_entrance_relative_LC_minors']+=1
                if n<=h+2:continue
                # The WHOLE outgoing triple is in the exact binary prefix.
                assert n-L<=h+1
                counts['actual_outgoing_exact_prefix_triples']+=1
                j=n-L
                if j<=0 or j%2==0:
                    counts['actual_valley_parity_transfers']+=1
                else:
                    assert D[n]**2>=D[n-1]*D[n+1]
                    counts['actual_peak_parity_ordinary_LC_payments']+=1
        if h>=L+2:
            for n in range(h+2,ell+1):
                assert D[n]**2>=D[n-1]*D[n+1]
                counts['actual_rising_tail_LC_beyond_uniform_entrance']+=1
        G=[];s=0
        for x in A:s+=x;G.append(s)
        best=1
        for n in range(4,Rnew+1):
            k=n-3
            if G[k]*G[best-1]<G[best]*G[k-1]:best=k
            assert G[best]*D[n-1]>=G[best-1]*D[n]
            counts['actual_ALL_C_current_ranks']+=1
            counts['actual_ALL_C_shifts_covered']+=k
        if case<400 and h>=L+3:
            Fparent=arm_prefix(alpha,[2]*(h-1),N+1)
            Apar=jump(Fparent,L,N)
            dp=[0,0]+[max(0,Apar[n]-Apar[n-1]) for n in range(2,N+1)]
            oldell=dp.index(max(dp))
            for n in range(h+3,ell):
                assert D[n+1]>D[n]
                assert dp[n-1]>dp[n-3]
                assert n-2<=oldell
                assert D[n]==dp[n-1]+dp[n-2]
                assert D[n-1]==dp[n-2]+dp[n-3]
                assert D[n+1]<=dp[n]+dp[n-1]
                counts['actual_strict_window_lifts_inside_old_FIRST_mode']+=1
        counts['actual_one_jump_arms']=counts.get('actual_one_jump_arms',0)+1
    out=dict(status='PASS_EXACT_QA_UNIFORM_ANALYTIC_GENERAL_ONE_JUMP_C',counts=dict(counts),
        seconds=time.monotonic()-start,
        scope='Finite exact actual QA only. The claimed all-capacity/all-count theorem requires the separate unbounded modified-tail/valley-parity/uniform-entrance/rising-tail/C-seed assembly and scoped Lean kernels. No original coefficient UI conclusion.')
    (ROOT/'audit_general_one_jump_analytic_C.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
