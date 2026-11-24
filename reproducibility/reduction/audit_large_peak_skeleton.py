"""Independent integer-coefficient audit of the arbitrary-skeleton peak bound.

Finite tests diagnose the analytic proof; they are not the proof of its
unbounded quantifiers. No symbolic solver is used by this audit.
"""
from pathlib import Path
import sys, json, random, time
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from probe_uncovered_short_skeleton import arm
from audit_short_arm import at, window, kernel, unimodal
from audit_joint_structure import fastconv


def add(*ps):
    return [sum(at(p, j) for p in ps) for j in range(max(map(len, ps)))]


def scale(p, c):
    return [c*x for x in p]


def conv(p, q):
    out = [0]*(len(p)+len(q)-1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i+j] += x*y
    return out


def data(U):
    C, R = [0], [1]
    for t in U:
        C = add([1], [0]+window(C, t))
        R = [0]+window(R, t)
    K = add(C, scale([0]+C, -1), R)
    return R, K


def kernels(U, V):
    RA, KA = data(U)
    RB, KB = data(V)
    P, X, Y, XY = (conv(KA, KB), conv(RA, KB),
                    conv(KA, RB), conv(RA, RB))
    E, D = [-1, 2], [1, -2, 1]
    return [add(conv(D, add(KA, KB)), conv(E, P)),
            scale(add(conv(D, RA), conv(E, X)), -1),
            scale(add(conv(D, RB), conv(E, Y)), -1), conv(E, XY),
            scale(P, -1), X, Y, scale(XY, -1)]


def coeff(q, n):
    return sum(c*max(n-j+1, 0) for j, c in enumerate(q))


def main():
    start = time.monotonic()
    rng = random.Random(2026101701)
    cores = identities = bounds = concavity = envelopes = 0
    for case in range(1100):
        U = sorted(rng.choices(range(2, 13), k=rng.randrange(1, 6)))
        V = sorted(rng.choices(range(2, 13), k=rng.randrange(1, 6)))
        u, v, r, s = sum(U), sum(V), len(U), len(V)
        W, L = u+v, r+s
        M = 8*W+rng.randrange(2*W+1)
        alpha = rng.randrange(M, 3*M)
        gap = rng.randrange(M-3)
        beta = alpha+u-v+gap
        assert beta >= 1
        A, B = arm(alpha, U), arm(beta, V)
        P = fastconv(A, B)
        Q = fastconv(A, kernel(B, M))
        QR = fastconv(B, kernel(A, M))
        H = add(Q, B)
        assert unimodal(H) and unimodal(Q) and unimodal(QR)
        x, y, m = alpha+1, beta+1, M+1
        N, D = alpha+beta+W+M, alpha+beta+W
        diff = [at(H, n)-at(H, n-1) for n in range(N+2)]
        qs = kernels(U, V)
        offsets = [0, x, y, x+y, m, m+x, m+y, m+x+y]
        for n in [0, 1, D, D+1, N, N+1]+[rng.randrange(N+2) for _ in range(10)]:
            assert diff[n] == sum(coeff(q, n-o) for q, o in zip(qs, offsets))
            identities += 1
        RA, KA = data(U)
        RB, KB = data(V)
        assert min(KA) >= 0 and min(KB) >= 0
        c = sum(RA)*sum(RB)
        assert sum(KA)*sum(KB) == c
        mu0 = sum(j*a for j, a in enumerate(conv(KA, KB)))
        mu1 = sum(j*a for j, a in enumerate(conv(RA, KB)))
        mu2 = sum(j*a for j, a in enumerate(conv(KA, RB)))
        for n in range(-3, 2*W+4):
            fs = [coeff(q, n) for q in qs]
            assert fs[2] <= -c*n+c+mu2
            assert fs[5] <= c*max(n-r+1, 0)
            assert fs[6] <= c*max(n-s+1, 0)
            if n <= W-2:
                assert fs[3] <= c*(W-L-2)
            if n >= W:
                assert fs[0] == c*n-c-mu0
                assert fs[1] == -c*n+c+mu1
            if n >= W-1:
                assert fs[4] == -c*n-c+mu0
            bounds += 1
        if N > 3*M+8:
            for n in range(N//2+1, min((N+6*W+2)//2, N+1)+1):
                assert M+W < n < x+y+L
                assert diff[n] <= diff[n-1]
                concavity += 1
            for n in range((N+6*W+1)//2, D+1):
                t, d = n-y, m+x-y
                E = d-2*t+3*W-L-2+max(t-d-r+1, 0)+max(t-m-s+1, 0)
                assert diff[n] <= c*E <= 0
                envelopes += 1
            assert diff[D+1] <= 0
        cores += 1
    out = dict(status='PASS', scope='Independent exact finite diagnostics of the analytic arbitrary-skeleton theorem; not a replacement for its proof',
               arbitrary_skeleton_cores=cores, exact_padding_identities=identities,
               profile_bounds=bounds, central_concavity_comparisons=concavity,
               late_envelope_comparisons=envelopes, seed=2026101701,
               seconds=time.monotonic()-start)
    ROOT.joinpath('audit_large_peak_skeleton.json').write_text(json.dumps(out, indent=2), encoding='utf8')
    print(json.dumps(out), flush=True)


if __name__ == '__main__':
    main()
