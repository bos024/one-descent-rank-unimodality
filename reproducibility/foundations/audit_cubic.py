"""Exact diagnostics for the analytic skeleton-disparity reduction."""
from pathlib import Path
import json
import random
import time
from audit_short_arm import at, window, forward, kernel, differences, unimodal


def conv(p, q):
    """Exact integer encoding; the total coefficient mass prevents slot carry."""
    size = max(1, (sum(p) * sum(q)).bit_length() // 8 + 1)
    pp = int.from_bytes(b''.join(x.to_bytes(size, 'little') for x in p), 'little')
    qq = int.from_bytes(b''.join(x.to_bytes(size, 'little') for x in q), 'little')
    count = len(p) + len(q) - 1
    raw = (pp * qq).to_bytes(size * count, 'little')
    return [int.from_bytes(raw[i * size:(i + 1) * size], 'little') for i in range(count)]


def main():
    started = time.monotonic()
    rng = random.Random(2026101532)
    cases = reverse_positions = central_positions = 0
    min_difference_gap = None
    for m in (4, 5, 6, 7, 8, 10, 12, 16, 20):
        for length in (1, 2, 5, 9, 20):
            for kind in range(3):
                if kind == 0:
                    U = [2] * length
                elif kind == 1:
                    U = [m - 1] * length
                else:
                    U = sorted(rng.choices(range(2, m), k=length))
                u = sum(U)
                target = 4 * u + 3 * m - 12
                if kind == 0:
                    V = [2] * (target // 2)
                    if target % 2:
                        V[-1] = 3
                elif kind == 1:
                    V = [m - 1] * ((target + m - 2) // (m - 1))
                else:
                    V = []
                    while sum(V) < target:
                        V.append(rng.randrange(2, m))
                    V.sort()
                v = sum(V)
                beta = rng.choice((0, 1, 10, u + 2 * m))
                Y = [1] * beta + V
                b = beta + v
                R = b + m
                dy = kernel(forward(Y), m)
                delta = dy[::-1]
                excess = v - len(V)
                for k in range((excess + m) // 2):
                    assert at(delta, k + 1) >= at(delta, k)
                    reverse_positions += 1
                fu = forward(U)
                ru = [1]
                for t in U:
                    ru = [0] + window(ru, t)
                ku = [at(fu, i) - at(fu, i - 1) + at(ru, i - 1) for i in range(u + 2)]
                assert ku[-1] == 0 and min(ku) >= 0
                ku.pop()
                top = conv(ku, dy)
                bottom = conv(ru, dy)
                small = conv(fu, dy)
                for eta in sorted({4 - m, 0, m - 4}):
                    alpha = b + eta - u
                    assert alpha >= 1
                    long = [0] + window(bottom, alpha)
                    Q = [at(small, i) + at(long, i) for i in range(max(len(small), len(long)))]
                    diff = differences(Q)
                    assert unimodal(Q), (m, U, Y, eta)
                    for n in range(len(diff)):
                        assert at(diff, n) == at(top, n) - at(bottom, n - alpha - 1)
                    assert all(at(diff, n) >= 0 for n in range(b + 4))
                    for n in range(b + 4, R + u + 1):
                        gap = at(diff, n) - at(diff, n + 1)
                        assert gap >= 0, (m, U, V, beta, eta, n, gap)
                        min_difference_gap = gap if min_difference_gap is None else min(min_difference_gap, gap)
                        central_positions += 1
                    assert all(at(diff, n) <= 0 for n in range(R + u + 1, len(diff)))
                    cases += 1
        print(json.dumps(dict(peak=m, cases_so_far=cases)), flush=True)
    result = dict(status='PASS', scope='exact diagnostics only; general theorem is analytic',
                  seed=2026101532, cores=cases, reverse_growth_positions=reverse_positions,
                  central_monotonicity_positions=central_positions,
                  minimum_central_gap=min_difference_gap, seconds=time.monotonic()-started)
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
