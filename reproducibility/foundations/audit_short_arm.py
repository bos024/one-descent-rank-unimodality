"""Exact diagnostics for the all-peak single-skeleton theorem."""
from itertools import combinations_with_replacement
from pathlib import Path
import json
import random
import time


def at(p, k):
    return p[k] if 0 <= k < len(p) else 0


def window(p, length):
    out = [0] * (len(p) + length - 1)
    value = 0
    for i in range(len(out)):
        value += at(p, i) - at(p, i - length)
        out[i] = value
    return out


def forward(word):
    p = [1]
    for t in word:
        p = [1] + window(p, t)
    return p


def kernel(p, m):
    product = [0] + window(p, m)
    return [value - at(p, i) + int(i == 0) for i, value in enumerate(product)]


def differences(p):
    return [at(p, i) - at(p, i - 1) for i in range(len(p) + 1)]


def unimodal(p):
    falling = False
    for d in differences(p):
        if d < 0:
            falling = True
        elif d > 0 and falling:
            return False
    return True


def qpoly(dy, alpha, t):
    product = [0] + window(window(dy, alpha + 1), t)
    return [v + at(dy, i) for i, v in enumerate(product)]


def main():
    started = time.monotonic()
    rng = random.Random(2026101531)
    growth_hosts = growth_inequalities = cases = gaps = 0
    for length in range(8):
        for word in combinations_with_replacement(range(1, 11), length):
            q = forward(word)[::-1]
            nonones = sum(t > 1 for t in word)
            for j in range(nonones):
                assert (j + 1) * at(q, j + 1) >= (nonones - j) * at(q, j)
                growth_inequalities += 1
            growth_hosts += 1

    for m in range(4, 31):
        nonones = 3 * m - 7
        for kind in range(3):
            if kind == 0:
                tail = [2] * nonones
            elif kind == 1:
                tail = [m - 1] * nonones
            else:
                tail = sorted(rng.choices(range(2, m), k=nonones))
            beta = max(0, 7 * m - 18 - sum(tail))
            y = [1] * beta + tail
            b = sum(y)
            p = forward(y)
            q = p[::-1]
            dy = kernel(p, m)
            assert all(at(dy, i) <= at(dy, i + 1) for i in range(4 * m - 7))
            for eta in sorted({4 - m, 0, m - 4}):
                for t in sorted({2, m - 1}):
                    alpha = b + eta - t
                    Q = qpoly(dy, alpha, t)
                    assert unimodal(Q), (m, y, eta, t)
                    diff = differences(Q)
                    assert all(at(diff, i) >= 0 for i in range(b + 4))
                    R = b + m
                    for c in range(m - 3):
                        s = c + t - m
                        correction = 0 if s < 0 else sum(at(q, j) for j in range(s)) + 2 * at(q, s)
                        formula = (at(q, c) + sum(at(q, j) for j in range(c + 2, c + t + 1))
                                   - correction + at(dy, m - c + t - eta - 1)
                                   - at(dy, m - c - eta - 1))
                        actual = at(diff, R - c) - at(diff, R - c + 1)
                        assert actual == formula and actual > 0, (m, kind, eta, t, c, actual, formula)
                        gaps += 1
                    cases += 1
        print(json.dumps(dict(peak=m, cases_so_far=cases)), flush=True)

    # A failed stronger concavity assertion is recorded only to delimit scope.
    witness = None
    for m in range(4, 21):
        for _ in range(300):
            nonones = rng.randrange(0, m)
            y = [1] * rng.randrange(12) + sorted(rng.choices(range(2, m), k=nonones))
            b = sum(y)
            if b < 1:
                continue
            t = rng.randrange(2, m)
            eta = rng.randrange(4 - m, m - 3)
            alpha = b + eta - t
            if alpha < 0:
                continue
            Q = qpoly(kernel(forward(y), m), alpha, t)
            diff = differences(Q)
            R = b + m
            for c in range(m - 3):
                gap = at(diff, R - c) - at(diff, R - c + 1)
                if gap < 0:
                    witness = dict(peak=m, X=[1] * alpha + [t], Y=y, c=c,
                                   difference_gap=gap, actual_unimodality=unimodal(Q))
                    break
            if witness:
                break
        if witness:
            break
    result = dict(status='PASS', scope='diagnostics only; statements have analytic proofs',
                  seed=2026101531, growth_hosts=growth_hosts,
                  growth_inequalities=growth_inequalities, single_arm_cases=cases,
                  strict_gap_identities=gaps, outside_hypotheses_concavity_witness=witness,
                  seconds=time.monotonic() - started)
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
