"""Exact actual-product QA; the all-depth claims use written unbounded proofs."""
from pathlib import Path
import json, random, time
from audit_large_peak_skeleton import arm, at
from audit_joint_structure import fastconv

ROOT = Path(__file__).resolve().parent


def main():
    start = time.monotonic()
    rng = random.Random(2026102702)
    counts = dict(actual_pairs=0, both_rising_source_ratio_minors=0,
                  nonnegative_current_both_rising_nonrecoveries=0,
                  beyond_fifth_and_old_diagonal_nonrecoveries=0,
                  proper_zero_head_integer_budget_payments=0)
    for case in range(6000):
        alpha, h = rng.randrange(1,100), rng.randrange(2,80)
        beta = rng.randrange(1,100)
        V = sorted(rng.choices(range(2,35),k=rng.randrange(2,65)))
        X, Y = arm(alpha,[2]*h), arm(beta,V)
        P = fastconv(X,Y)
        Rx, Ry = X.index(max(X)), Y.index(max(Y))
        EY = [int(n==0)-int(n==1)+2*at(Y,n-1)-at(Y,n)
              for n in range(len(Y)+1)]
        H = fastconv(EY,X)
        q = next(n for n in range(2,len(EY)) if EY[n])
        for N in range(3,min(Rx,Ry)+1):
            D, Dp = X[N]-X[N-1], X[N-1]-X[N-2]
            assert D > 0 and Dp > 0
            ratio_minor = H[N]*Dp-H[N-1]*D
            assert ratio_minor >= 0,(alpha,h,beta,V,N)
            counts['both_rising_source_ratio_minors'] += 1
            e = 2*P[N-1]-P[N]
            M = 3*P[N-1]-P[N]-2*P[N-2]
            assert e == H[N]-D
            assert M == H[N]-H[N-1]-D+Dp
            if e >= 0:
                assert M >= 0,(alpha,h,beta,V,N,e,M)
                counts['nonnegative_current_both_rising_nonrecoveries'] += 1
                s, r = N-3-q, N-q
                if s >= 5 and q < max(s+4,8) and not (h >= r-1 and V[-1] >= r+1):
                    counts['beyond_fifth_and_old_diagonal_nonrecoveries'] += 1
        head = 2*P[-2]-3
        assert P[-2] >= 6
        for N in range(1,len(P)):
            e = 2*P[N-1]-P[N]
            if e not in (0,1):
                continue
            M = 3*P[N-1]-P[N]-2*at(P,N-2)
            assert head+M >= 0,(alpha,h,beta,V,N,e,M,head)
            counts['proper_zero_head_integer_budget_payments'] += 1
        counts['actual_pairs'] += 1
    assert counts['beyond_fifth_and_old_diagonal_nonrecoveries'] > 1000
    out = dict(status='PASS_EXACT_ALL_DEPTH_BINARY_C_PRODUCT_CONSEQUENCES_QA',
               counts=counts,seconds=time.monotonic()-start,
               scope='Exact finite QA only. Source-ratio, nonrecovery and zero-head '
                     'head-budget statements are distinguished. General C, remaining '
                     'mixed/incoming, A2 and original coefficient UI remain OPEN.')
    (ROOT/'audit_binary_C_product_consequences.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__ == '__main__':
    main()
