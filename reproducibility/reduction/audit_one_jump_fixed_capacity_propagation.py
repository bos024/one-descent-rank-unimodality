"""Actual exact QA beyond every finite entrance, plus padding/mode/seed checks."""
from pathlib import Path
from random import Random
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from collections import Counter
import json,time
ROOT=Path(__file__).resolve().parent


def main():
    start=time.monotonic();rng=Random(20261027124);counts=Counter()
    fib=[0,1]
    for n in range(1000):fib.append(fib[-1]+fib[-2])
    for case in range(1000):
        L=rng.randint(3,32);h=rng.randint(L+3,200);alpha=rng.randint(1,600);N=2*h+L
        F=arm_prefix(alpha,[2]*h+[L],N+1)
        clamped=arm_prefix(min(alpha,h+L),[2]*h+[L],N+1)
        assert F==clamped
        D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,N+2)]
        R=next(i for i in range(2,N+2) if D[i]==0)-1
        assert all(D[i]==0 for i in range(R+1,N+2)) and R<=N
        r=[0,0]+[fib[n]-(fib[n-L] if n>=L else 0) for n in range(2,N+2)]
        C=fib[L-1]+fib[L+1]-1-(-1)**L
        assert r[h]>=C and D[:h+3]==r[:h+3]
        assert D[h+3]<=r[h+3]-1
        for n in range(h+2,R+1):
            assert D[n]**2>=D[n-1]*D[n+1]
            counts['actual_FULL_tail_minors_beyond_entrance']+=1
        if D[h+3]>0:
            assert D[h+2]*D[h+1]>=D[h+3]*D[h]
            assert D[h+2]**2>=D[h+3]*D[h+1]
            assert F[h]*D[h+2]>=F[h-1]*D[h+3]
            counts['actual_complete_first_defect_seed_sets']+=1
        G=[];s=0
        for x in F:s+=x;G.append(s)
        best=1
        for n in range(4,R+1):
            k=n-3
            if G[k]*G[best-1]<G[best]*G[k-1]:best=k
            assert G[best]*D[n-1]>=G[best-1]*D[n]
            counts['actual_C_current_ranks_beyond_entrance']+=1
            counts['actual_C_shifts_covered_beyond_entrance']+=k
        # Identity (3) for signed slopes: compares genuinely different
        # actual sorted words, adding the two before fixed L.
        Fnew=arm_prefix(alpha,[2]*(h+1)+[L],N+3)
        old_signed=[F[n]-F[n-1] for n in range(2,N+2)]
        new_signed=[Fnew[n]-Fnew[n-1] for n in range(2,N+4)]
        for j in range(h+1,N):
            assert new_signed[j]==old_signed[j-1]+old_signed[j-2]
            counts['actual_signed_h_recursion_tail_edges']+=1
        counts['actual_profiles_beyond_entrance']+=1
    out=dict(status='PASS_EXACT_ONE_JUMP_FIXED_CAPACITY_UNBOUNDED_PROPAGATION_QA',counts=dict(counts),
        seconds=time.monotonic()-start,
        scope='Finite actual QA beyond ALL entrance count bounds, separate from the generic unbounded Lean/written proof and complete independent entrance certificate. No arbitrary-capacity or original UI claim.')
    (ROOT/'audit_one_jump_fixed_capacity_propagation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
