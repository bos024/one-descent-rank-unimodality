"""Exact diagnostic of an auxiliary conjecture, not an original-C certificate."""
from pathlib import Path
from random import Random
from collections import Counter
import hashlib, json, time
from audit_arbitrary_Fibonacci_tail_late_C import add, sub, mul, sign

Q = (-1, 1)
PHI = (0, 1)
ZERO = (0, 0)


def minor(a, n):
    return sub(mul(a[n], a[n]), mul(a[n-1], a[n+1]))


def fixed_counter():
    b=[233,2257,13100,19891,30200,39423,50487,61489,73673,86341,
       100000,83454,63229]
    h=len(b)-1
    assert all(b[n]**2>=b[n-1]*b[n+1] for n in range(1,h))
    E=[add((b[n] if n<=h else 0,0),
           mul(Q,(b[n-1] if n else 0,0))) for n in range(h+2)]
    assert all(sign(minor(E,n))>=0 for n in range(1,len(E)-1))
    d=[]
    for n,v in enumerate(E):
        z=sub(v,E[n-1] if n else ZERO)
        if sign(z)<=0:break
        d.append(z)
    assert len(d)==11
    assert all(sign(minor(d,n))>0 for n in range(1,len(d)-1))
    x=[ZERO]*(h+2)
    for n in range(h,-1,-1):
        x[n]=mul(Q,add(x[n+1],(b[n+1] if n<h else 0,0)))
    assert all(sign(minor(x,n))>=0 for n in range(1,h))
    A=[sub(x[n],E[n]) for n in range(h+2)]
    A=[v if sign(v)>0 else ZERO for v in A]
    assert all(sign(sub(A[3],v))>0 for n,v in enumerate(A) if n!=3)
    M=minor(A,2)
    assert M==(-205686371365,127116786985) and sign(M)<0
    return dict(b=b,alpha=1,first_mode=3,n=2,A_triple=A[1:4],margin=M,
        exact_positive_E_primitive_minors=[minor(d,n) for n in range(1,len(d)-1)],
        meaning='Disproves the auxiliary LC-b plus positive-primitive-LC-E geometric-cut closure, even before the first A mode. E is not a CI polynomial; this is NOT an original or actual-CI counterexample.')


def main():
    started = time.monotonic()
    rng = Random(20261029732)
    counts = Counter()
    sha = hashlib.sha256()
    counter = None
    stronger_counter = None
    for trial in range(30000):
        h = rng.randint(5, 55)
        denominator = rng.choice([8, 16, 24])
        ratios = sorted([rng.randint(1, 4*denominator) for _ in range(h)], reverse=True)
        b = [denominator**h]
        for v in ratios:
            b.append(b[-1]*v//denominator)
        assert all(b[n]**2 >= b[n-1]*b[n+1] for n in range(1,h))
        E = [add((b[n] if n <= h else 0, 0),
                 mul(Q, (b[n-1] if n else 0, 0))) for n in range(h+2)]
        delta = []
        for n, value in enumerate(E):
            v = sub(value, E[n-1] if n else ZERO)
            if sign(v) <= 0:
                break
            delta.append(v)
        if any(sign(minor(delta,n)) < 0 for n in range(1,len(delta)-1)):
            continue
        counts['eligible_LC_b_and_positive_primitive_LC_E'] += 1
        alpha = rng.randint(1,min(h,16))
        x = [ZERO]*(h+2)
        for n in range(h,-1,-1):
            x[n] = mul(Q,add(x[n+1],(b[n+1] if n<h else 0,0)))
        raw = [sub(x[n],E[n-alpha+1] if 0<=n-alpha+1<len(E) else ZERO)
               for n in range(h+2)]
        A = [v if sign(v)>0 else ZERO for v in raw]
        ell = 0
        for n in range(1,len(A)):
            if sign(sub(A[n],A[ell]))>0:
                ell=n
        c = [sub(mul(PHI,A[n-1] if n else ZERO),A[n]) for n in range(len(A))]
        for n in range(1,ell+1):
            margin=minor(A,n)
            counts['finite_only_through_first_mode_A_LC_minors'] += 1
            if sign(margin)<0:
                counter=dict(trial=trial,b=b,denominator=denominator,ratios=ratios,
                             alpha=alpha,mode=ell,n=n,A_triple=A[n-1:n+2],margin=margin)
                break
        if stronger_counter is None:
            for n in range(2,ell+1):
                if min(sign(v) for v in c[n-1:n+2])>0 and sign(minor(c,n))<0:
                    stronger_counter=dict(trial=trial,b=b,denominator=denominator,ratios=ratios,
                        alpha=alpha,mode=ell,n=n,c_triple=c[n-1:n+2],margin=minor(c,n))
                    break
        sha.update(json.dumps([b,alpha,A,ell],separators=(',',':')).encode())
        if counter:
            break
    out=dict(status='DISPROVED_GENERIC_GEOMETRIC_CUT_LC_BY_EXACT_FIXED_COUNTER',
        counts=dict(counts),random_search_counter=counter,
        fixed_counter=fixed_counter(),stronger_deficit_LC_counter=stronger_counter,
        state_sha256=sha.hexdigest(),seconds=time.monotonic()-started,
        scope='The generic auxiliary condition is FALSE by the exact fixed counter, despite the recorded finite random nonfailures. No CI spectral-boundary assembly, no actual-CI counterexample, no general C/A2/original UI claim.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['fixed_counter','random_search_counter','stronger_deficit_LC_counter']}),flush=True)
    for key in ['fixed_counter','random_search_counter','stronger_deficit_LC_counter']:
        v=out[key]
        print(key, None if v is None else {k:z for k,z in v.items() if k not in ['b','A_triple','c_triple','margin']},flush=True)


if __name__=='__main__':
    main()
