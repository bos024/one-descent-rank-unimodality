"""Exact actual-word QA of the full binary ordinary tail and dominant-jump C."""
from pathlib import Path
from random import Random
from audit_minimum_staircase_scaled_dyadic import arm_prefix
import json,time
ROOT=Path(__file__).resolve().parent


def main():
    start=time.monotonic();rng=Random(20261027122);counts={}
    fib=[0,1]
    for n in range(1200):fib.append(fib[-1]+fib[-2])
    for case in range(1600):
        alpha=rng.randint(1,180);h=rng.randint(1,110);W=alpha+2*h
        F=arm_prefix(alpha,[2]*h,W+2);R=F.index(max(F))
        assert R<=2*h
        for n in range(h+2):assert F[n]==fib[n+1]
        assert F[h+2]<=fib[h+3]-1
        for n in range(h+1,W+2):
            minor=F[n]**2-F[n-1]*F[n+1]
            assert minor>=0
            if F[n]>F[n-1]:assert minor>=1
            counts['full_binary_ordinary_tail_minors']=counts.get('full_binary_ordinary_tail_minors',0)+1
        for n in range(1,R+1):
            assert F[n]**2*fib[n]*fib[n+2]>=F[n-1]*F[n+1]*fib[n+1]**2
            counts['binary_ordinary_relative_LC_minors']=counts.get('binary_ordinary_relative_LC_minors',0)+1
        capacities={max(3,R),max(3,R+1),2*h+1,rng.randint(max(3,R),max(3,R)+100)}
        for L in sorted(capacities):
            N=W+L
            A=arm_prefix(alpha,[2]*h+[L],N)
            D=[0,0]+[max(0,A[n]-A[n-1]) for n in range(2,N+1)]
            ell=D.index(max(D));assert ell<=R+1
            for n in range(2,min(L,R+1)+1):assert D[n]==F[n-1]
            if L==R:assert D[R+1]==F[R]-1
            G=[];s=0
            for x in A:s+=x;G.append(s)
            # All nontrivial rising comparisons; falling/flat ratios have
            # direct nonnegative cumulative payment, at EVERY later rank.
            for n in range(3,ell+1):
                if D[n]<=D[n-1]:continue
                for shift in range(3,n):
                    k=n-shift
                    assert G[k]*D[n-1]>=G[k-1]*D[n]
                    counts['ALL_nondegenerate_C_shifts']=counts.get('ALL_nondegenerate_C_shifts',0)+1
            counts['actual_dominant_one_jump_arms']=counts.get('actual_dominant_one_jump_arms',0)+1
            if L==R:counts['exact_mode_boundary_arms']=counts.get('exact_mode_boundary_arms',0)+1
        counts['actual_binary_prefixes']=counts.get('actual_binary_prefixes',0)+1
    out=dict(status='PASS_EXACT_BINARY_ORDINARY_TAIL_AND_DOMINANT_ONE_JUMP_C_QA',counts=counts,
        seconds=time.monotonic()-start,
        scope='Finite exact actual-word QA only. Separate unbounded polynomial recurrence/tail induction and normalized-relative-C transfer prove the declared families. No theorem for smaller jumps, general C/A2/original UI.')
    (ROOT/'audit_binary_ordinary_tail_and_one_jump_C.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
