"""Exact QA of the conditional actual source-prefix/window theorem."""
from pathlib import Path
from collections import Counter
import random, json, time
from audit_joint_structure import fastconv
from probe_double_defect_tail_recovery import prefix

ROOT = Path(__file__).resolve().parent


def arm(alpha, u):
    a, _ = prefix(alpha,u,alpha+sum(u))
    return a[::-1]


def source(p):
    return [2*p[0]]+[2*p[i]-p[i-1] for i in range(1,len(p))]+[-p[-1]]


def first_missing(q):
    f = q[::-1]
    return next(n for n in range(1,len(f)+1)
                if (f[n] if n<len(f) else 0) < 2**(n-1))


def main():
    start = time.monotonic()
    rng = random.Random(2026102619)
    counts = Counter()
    witness = None
    for rep in range(4000):
        alpha, beta = rng.randrange(1,100), rng.randrange(1,100)
        u = sorted(rng.choices(range(2,26), k=rng.randrange(2,13)))
        v = sorted(rng.choices(range(2,26), k=rng.randrange(2,13)))
        a, b = arm(alpha,u), arm(beta,v)
        c, bwt = len(a)-1, len(b)-1
        d, M = c+bwt, max(c,bwt)
        p = fastconv(a,b)
        e = source(p)
        first = p.index(max(p))
        last = max(i for i,x in enumerate(p) if x==max(p))
        assert all(e[r]>=0 for r in range(M))
        counts['actual_source_prefix_nonnegative_coefficients'] += M
        for r in range(d//2,M-1):
            assert e[r+1] <= e[r]
            counts['actual_upper_half_source_monotonic_edges'] += 1
        premise = all(e[r+1]<=e[r] for r in range(last+1,d//2+1) if e[r]>=0)
        if not premise:
            counts['old_half_weak_premise_failed'] += 1
            continue
        counts['old_half_weak_premise_passed'] += 1
        assert all(e[r+1]<=e[r] for r in range(first,M-1))
        counts['assembled_post_mode_source_prefix_edges'] += max(0,M-1-first)
        t = max(max(u),bwt-c,2)+rng.randrange(13)
        newa = arm(alpha,u+[t])
        new = fastconv(newa,b)
        enew = source(new)
        nfirst = new.index(max(new))
        nlast = max(i for i,x in enumerate(new) if x==max(new))
        for n in range(nfirst,min(M-1,len(new)-1)):
            if enew[n+1] > enew[n]:
                witness = dict(alpha=alpha,U=u,beta=beta,V=v,c=c,b=bwt,t=t,
                               n=n,old_premise=True,source=enew[n:n+2])
                break
            assert enew[n]>=0
            counts['conditional_actual_transported_tail_edges'] += 1
        if witness:
            break
        if c >= bwt+t+3:
            counts['fully_covered_unbalanced_contexts'] += 1
            for n in range(nlast+1,(len(new)-1)//2+1):
                assert n+1<M
                assert enew[n+1]<=enew[n]
                counts['fully_covered_unbalanced_new_half_tail_edges'] += 1
        if c >= bwt:
            kappa, short_h = first_missing(a), len(v)
        else:
            kappa, short_h = first_missing(b), len(u)
        short = min(c,bwt)
        short_main_degree = short-short_h
        new_heavier = c+t
        for n in range(nlast+1,(len(new)-1)//2+1):
            assert enew[n+1] <= enew[n]
            assert enew[n] >= 0
            counts['actual_complete_new_half_tail_edges'] += 1
            if n+1 >= new_heavier:
                counts['proof_branch_new_terminal_edge'] += 1
                continue
            k = n+1-t
            assert k < c <= M
            if k <= last:
                counts['proof_branch_crossing_concavity'] += 1
            elif n <= M-2:
                counts['proof_branch_old_positive_prefix'] += 1
            elif n == M-1:
                counts['proof_branch_first_source_boundary'] += 1
            else:
                r = n-M
                assert r >= 0
                if r+3 >= kappa:
                    counts['proof_branch_late_source_layer'] += 1
                elif short_main_degree >= kappa+r-1:
                    counts['proof_branch_short_main_box'] += 1
                elif short-r+1 < M and kappa <= M-short+2*r+1:
                    counts['proof_branch_virtual_central_head'] += 1
                else:
                    # The proved mass/normalization arithmetic excludes this.
                    raise AssertionError(('UNPAID_PROOF_STATE',c,bwt,t,n,kappa,
                                          short_h,short_main_degree))
        counts['actual_pairs'] += 1
    out = dict(status='CONDITIONAL_TRANSPORT_COUNTEREXAMPLE' if witness else
                      'PASS_EXACT_QA_OF_ACTUAL_HALF_TAIL_CURVATURE_ASSEMBLY',
               counts=dict(counts), witness=witness, seconds=time.monotonic()-start,
               scope='Finite QA only. The complete unbounded actual induction is in '
                     'agent_half_lc_actual_weak_curvature.tex. OLD-W is tested here '
                     'as the old induction premise; no OLD A1 or actual half-LC '
                     'is assumed. General S and original UI remain OPEN.')
    (ROOT/'agent_half_lc_weak_window_transport.json').write_text(
        json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__ == '__main__':
    main()
