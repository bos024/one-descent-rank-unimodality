"""Exact diagnostics for a proposed UNBOUNDED binary-C proof.

Finite checks are not the unbounded proof.  They deliberately include the
larger arbitrary-last-trimmed family and rational, noninteger density models.
"""
from pathlib import Path
from fractions import Fraction as Q
import json, random, time
from audit_large_peak_skeleton import arm

ROOT = Path(__file__).resolve().parent


def at(a, n):
    return a[n] if 0 <= n < len(a) else 0


def fibs(n):
    f = [0, 1]
    for _ in range(n):
        f.append(f[-1] + f[-2])
    return f


def mulpoly(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def main():
    start = time.monotonic()
    rng = random.Random(2026102701)
    f = fibs(400)
    count = dict(actual_terminal_trims=0, actual_relative_LC=0,
                 arbitrary_trims=0, arbitrary_tail_LC=0,
                 arbitrary_strict_tail_LC=0, arbitrary_relative_LC=0,
                 exact_model_polynomial_coefficients=0,
                 exact_model_scalar_payments=0,
                 rational_density_C=0, actual_binary_C=0)
    for alpha in range(1, 51):
        old = [1]*(alpha+1)
        d = []
        for h in range(1, 61):
            F = [1] + [at(old, n-1)+at(old, n-2)
                       for n in range(1, len(old)+2)]
            dn = [max(0, F[n]-F[n-1]) for n in range(2, len(F))]
            while dn and dn[-1] == 0:
                dn.pop()
            if h == 1:
                assert dn == [1]
            else:
                raw = [1] + [at(d, n-1)+at(d, n-2)
                             for n in range(1, len(d)+2)]
                assert dn[:-1] == raw[:len(dn)-1]
                assert len(dn) in (len(raw), len(raw)-1)
                assert at(dn, len(raw)-1) <= raw[-1]
                assert dn == raw[:len(raw)-1]+[dn[-1]] or dn == raw[:-1]
                count['actual_terminal_trims'] += 1
            assert all(dn[n] == f[n+1] for n in range(h))
            assert at(dn, h) < f[h+1]
            for n in range(1, len(dn)):
                assert dn[n]**2*f[n]*f[n+2] >= at(dn,n-1)*at(dn,n+1)*f[n+1]**2
                count['actual_relative_LC'] += 1
            G = []
            run = 0
            for x in F:
                run += x
                G.append(run)
            D = [0, 0]+dn
            for N in range(3, len(D)):
                if D[N] <= D[N-1]:
                    continue
                for R in range(3, N+1):
                    k = N-R
                    assert G[k]*D[N-1] >= at(G,k-1)*D[N], (alpha,h,N,R)
                    count['actual_binary_C'] += 1
            old, d = F, dn
    for _ in range(500):
        d = [1]
        for h in range(1, 71):
            assert all(d[n] == f[n+1] for n in range(h))
            assert at(d, h) < f[h+1]
            for n, x in enumerate(d):
                assert x <= f[n+1]
                if n >= h-1:
                    assert x*x >= at(d,n-1)*at(d,n+1)
                    count['arbitrary_tail_LC'] += 1
                if n >= h:
                    assert x*x >= at(d,n-1)*at(d,n+1)+1
                    count['arbitrary_strict_tail_LC'] += 1
                if n >= 1:
                    assert x*x*f[n]*f[n+2] >= at(d,n-1)*at(d,n+1)*f[n+1]**2
                    count['arbitrary_relative_LC'] += 1
            raw = [1]+[at(d,n-1)+at(d,n-2) for n in range(1,len(d)+2)]
            raw[-1] = rng.randrange(raw[-1]+1)
            if not raw[-1]:
                raw.pop()
            d = raw
            count['arbitrary_trims'] += 1
    def Gmodel(k):
        if k < 0:
            return [0]
        out = [k+1]
        for i in range(2,k+1):
            power = max(0,i-3)
            out += [0]*max(0,power+1-len(out))
            out[power] += (k-i+1)*f[i-1]
        return out
    for k in range(3, 121):
        for offset in (0,1):
            A, B = f[k+1+offset], f[k+2+offset]
            g, gp = Gmodel(k), [0]+Gmodel(k-1)
            phi = [A*at(g,j)-B*at(gp,j) for j in range(max(len(g),len(gp)))]
            assert phi[0] > 0 and phi[1] < 0
            for j in range(2,len(phi)):
                assert phi[j] == (k-j-2)*(-1)**(j+1)*f[k-j+offset],(k,offset,j)
                count['exact_model_polynomial_coefficients'] += 1
            for j in range(2,len(phi),2):
                assert phi[j] <= 0
                if j+1 < len(phi):
                    assert phi[j+1] >= 0
                    assert j*(-phi[j]) >= (j+1)*phi[j+1]
            expected = f[k]-(-1)**(k+1) if offset == 0 else f[k+1]
            assert sum(phi) == expected >= 0
            for a in (Q(0),Q(1,7),Q(1,2),Q(2,3),Q(9,10),Q(1)):
                value = sum(c*a**j for j,c in enumerate(phi))
                assert value >= expected
                count['exact_model_scalar_payments'] += 1
    for _ in range(1000):
        rho = [Q(1)]*4
        ratio = Q(1)
        Nmax = rng.randrange(8,42)
        for n in range(4,Nmax+1):
            ratio *= Q(rng.randrange(8,13),12)
            rho.append(rho[-1]*ratio)
        D = [Q(0),Q(0)]+[f[n-1]*rho[n] for n in range(2,Nmax+1)]
        F, G = [Q(1)], [Q(1)]
        for n in range(1,Nmax+1):
            F.append(F[-1]+D[n])
            G.append(G[-1]+F[-1])
        for N in range(3,Nmax+1):
            for R in range(3,N+1):
                k = N-R
                assert G[k]*D[N-1] >= at(G,k-1)*D[N],(N,R)
                count['rational_density_C'] += 1
    out = dict(status='PASS_EXACT_BINARY_RELATIVE_FIBONACCI_AND_C_QA',
               counts=count, seconds=time.monotonic()-start,
               scope='Finite exact diagnostics only. Arbitrary terminal trimming, '
                     'rational relative-LC class and all-index model formulas are '
                     'tested separately. Unbounded proofs require companion TeX/Lean; '
                     'general C, A2 and original conjecture are not proved here.')
    (ROOT/'audit_binary_relative_fibonacci_C.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__ == '__main__':
    main()
