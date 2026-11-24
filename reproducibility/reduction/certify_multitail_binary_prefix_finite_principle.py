"""Exact finite entrances for the WRITTEN fixed-tail unbounded C principle.

Every alpha/u representative is exhaustive, not a random sample.  Prefix
minimum G ratios check ALL shifts in O(N) exact integer comparisons.  A
separate literal double loop cross-checks selected representatives.
"""
from pathlib import Path
from collections import Counter
from itertools import accumulate
import argparse, hashlib, json, time
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_arbitrary_Fibonacci_tail_late_C import append_reference

ROOT=Path(__file__).resolve().parent


def words(remaining, least=3, prefix=()):
    for t in range(least, remaining+1):
        V=prefix+(t,)
        yield V
        yield from words(remaining-t,t,V)


def c_check(F, D, M, counts, literal=False):
    G=list(accumulate(F));best=None
    for N in range(3,M+1):
        k=N-3
        if k>=1:
            if best is None or G[k]*G[best-1]<G[best]*G[k-1]:best=k
        if D[N]<=D[N-1]:continue
        if best is not None:
            minor=G[best]*D[N-1]-G[best-1]*D[N]
            assert minor>=0,('C',N,best,minor)
            counts['exact_prefix_minimum_ALL_shift_C_payments']+=1
        counts['ALL_C_shifts_covered_at_increasing_current_ranks']+=max(0,N-3)
        if literal:
            for j in range(1,N-2):
                assert G[j]*D[N-1]>=G[j-1]*D[N],('literalC',N,j)
                counts['independent_literal_ALL_shift_C_checks']+=1


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--weight',type=int,default=24)
    args=ap.parse_args();bound=args.weight
    start=time.monotonic();counts=Counter();certs=[];digest=hashlib.sha256()
    for wi,V in enumerate(words(bound),1):
        W=sum(V);r=len(V);h=W-r;H=h+4;M=2*H+W
        # All finite early reference comparisons, independent of actual padding.
        ref=[1,1]
        for n in range(2,max(M+2,W+8)):ref.append(ref[-1]+ref[-2])
        for t in V:ref=append_reference(ref,t)
        rd=[0,0]+[ref[n]-ref[n-1] for n in range(2,len(ref))]
        c_check(ref,rd,W+5,counts,literal=(wi%97==1))
        counts['complete_early_reference_profiles']+=1
        # Check the unbounded analytic Cassini budget with exact integers.
        A=abs(rd[W+3]**2-rd[W+2]*rd[W+4])
        assert A>0 and rd[W+2]>=A and rd[W+4]>=2*A+1
        counts['whole_word_Cassini_amplitude_and_seed_budgets']+=1
        local=Counter()
        for u in range(H+1):
            mode_bound=2*u+W;alpha_bound=u+h+1
            for alpha in range(1,alpha_bound+1):
                F=arm_prefix(alpha,[2]*u+list(V),mode_bound+1)
                D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
                assert D[mode_bound+1]==0,('modebound',V,u,alpha)
                ell=D.index(max(D))
                if u==H:
                    N0=u+r+2
                    assert F[:N0]==ref[:N0]
                    assert ref[N0]-F[N0]==(2 if alpha==1 else 1)
                    for n in range(N0-1,ell):
                        minor=D[n]**2-D[n-1]*D[n+1]
                        assert minor>=0,('LCentrance',V,u,alpha,n,minor)
                        counts['exhaustive_entrance_rising_tail_LC_minors']+=1
                        local['LC_minors']+=1
                    counts['exhaustive_entrance_alpha_representatives']+=1
                    local['entrance_profiles']+=1
                    # C at H follows analytically; independently check it too.
                    c_check(F,D,mode_bound,counts,literal=(wi%97==1 and alpha in (1,alpha_bound)))
                else:
                    c_check(F,D,mode_bound,counts,literal=(wi%97==1 and alpha in (1,alpha_bound)))
                    counts['exhaustive_shorter_binary_count_alpha_representatives']+=1
                    local['shorter_profiles']+=1
                if alpha==alpha_bound:
                    Fbig=arm_prefix(alpha_bound+mode_bound+17,[2]*u+list(V),mode_bound+1)
                    assert Fbig==F,('paddingclamp',V,u)
                    counts['independent_padding_clamp_prefix_checks']+=1
                digest.update(json.dumps([V,u,alpha,F,D,ell],separators=(',',':')).encode())
        certs.append(dict(V=V,W=W,H=H,alpha_entrance_bound=H+h+1,
            rank_entrance_bound=M+1,Cassini_amplitude=A,counts=dict(local)))
        counts['ALL_sorted_nonbinary_tail_words']+=1
        if r>=6:counts['tail_words_with_at_least_six_nonbinary_capacities']+=1
        if wi%100==0:print(json.dumps(dict(words=wi,seconds=round(time.monotonic()-start,2))),flush=True)
    out=dict(status='PASS_EXHAUSTIVE_FIXED_MULTITAIL_FINITE_ENTRANCES',
        nonbinary_tail_weight_bound=bound,counts=dict(counts),
        complete_state_sha256=digest.hexdigest(),certificates=certs,
        seconds=time.monotonic()-start,
        conclusion='Via the written unbounded finite principle, COMPLETE C for EVERY sorted actual 1^alpha 2^u V with sum(V)<=bound, ALL alpha>=1 and u>=0. V entries>=3. Binary-empty-tail case is the previous binary theorem. No general original/A2 claim; no original numerical-bound upgrade.',
        scope='Exact exhaustive representatives plus a written universal propagation theorem, not an end-to-end Lean proof of all finite words. Prefix-minimum ratios cover ALL shifts; selected cases separately checked literally. State hash is for independent reconstruction.')
    target=ROOT/f'multitail_binary_prefix_finite_entrance_weight{bound}.json'
    target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='certificates'}),flush=True)


if __name__=='__main__':main()
