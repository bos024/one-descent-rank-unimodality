"""Exact Hilbert-growth checks and explicit monomial SLP realizations.

The unbounded algebraic argument is in ordinary_lefschetz_realization.tex.
No claim about a general one-descent core is made here.
"""
from pathlib import Path
from math import comb
from collections import Counter
import json,random,sys,time
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT))
from audit_large_peak_skeleton import arm,fastconv,at,window,unimodal

def positive_delta(h):
    d=[h[0]]+[max(h[j]-h[j-1],0) for j in range(1,len(h))]
    while len(d)>1 and d[-1]==0:d.pop()
    return d

def macaulay_next(x,degree):
    if not x:return 0
    remaining=x;out=0;upper=None
    for d in range(degree,0,-1):
        if not remaining:break
        lo=d
        if upper is None:
            hi=d+1
            while comb(hi,d)<=remaining:hi=2*hi+1
        else:hi=upper+1
        while lo+1<hi:
            mid=(lo+hi)//2
            if comb(mid,d)<=remaining:lo=mid
            else:hi=mid
        k=lo
        assert comb(k,d)<=remaining
        remaining-=comb(k,d)
        out+=comb(k+1,d+1)
        upper=k-1
    assert remaining==0
    return out

def is_osequence(h):
    return h[0]==1 and all(at(h,j+1)<=macaulay_next(h[j],j) for j in range(1,len(h)))

def monomials(variables,degree):
    if variables==0:
        return [()] if degree==0 else []
    if variables==1:return [(degree,)]
    return [(i,)+m for i in range(degree+1) for m in monomials(variables-1,degree-i)]

def realization(h):
    """Lift lex standard monomials of Delta+ h to nested z chains."""
    assert unimodal(h)
    g=positive_delta(h)
    assert is_osequence(g)
    variables=at(g,1)
    base=[]
    for j,count in enumerate(g):
        layer=monomials(variables,j)
        assert len(layer)>=count
        base.extend(layer[:count])
    base.sort(key=lambda m:(sum(m),m))
    base_set=set(base)
    for m in base:
        for i,e in enumerate(m):
            if e:
                lower=list(m);lower[i]-=1
                assert tuple(lower) in base_set
    peak=h.index(max(h))
    ends=[]
    for j in range(len(h)-1,peak-1,-1):
        ends.extend([j]*(h[j]-at(h,j+1)))
    assert len(ends)==len(base)
    intervals=[];basis=set()
    for m,end in zip(base,ends):
        degree=sum(m)
        assert degree<=peak<=end
        intervals.append((degree,end))
        for k in range(end-degree+1):basis.add(m+(k,))
    # Check the actual order-ideal property, not just its degree counts.
    for m in basis:
        for i,e in enumerate(m):
            if e:
                lower=list(m);lower[i]-=1
                assert tuple(lower) in basis
    histogram=Counter(map(sum,basis))
    assert [histogram[j] for j in range(len(h))]==h
    ranks=0
    for i in range(len(h)):
        for j in range(i,len(h)):
            # Distinct surviving z strings give distinct nonzero images.
            rank=sum(l<=i and j<=r for l,r in intervals)
            assert rank==min(h[i],h[j])
            ranks+=1
    return len(basis),ranks

def main():
    rng=random.Random(2026102097)
    start=time.monotonic()
    profiles=mac_tests=ratio_tests=0
    for case in range(1800):
        alpha,beta=rng.randrange(1,70),rng.randrange(1,70)
        U=rng.choices(range(2,19),k=rng.randrange(0,11))
        V=rng.choices(range(2,19),k=rng.randrange(0,11))
        A,B=arm(alpha,U)[::-1],arm(beta,V)[::-1]
        for q,r in [(A,len(U)+1),(fastconv(A,B),len(U)+len(V)+2)]:
            if case%3==0:
                t=rng.randrange(2,20)
                q=window(q,t)
                r+=1
            assert unimodal(q)
            g=positive_delta(q)
            assert is_osequence(q) and is_osequence(g)
            assert at(g,1)==r-1
            for j in range(len(g)):
                assert (j+1)*at(g,j+1)<=(r-1+j)*g[j]
                ratio_tests+=1
            mac_tests+=len(q)+len(g)-2
            profiles+=1
    algebra_cases=basis_monomials=power_map_ranks=0
    for case in range(50):
        alpha,beta=rng.randrange(1,4),rng.randrange(1,4)
        U=rng.choices(range(2,5),k=rng.randrange(0,3))
        V=rng.choices(range(2,5),k=rng.randrange(0,3))
        q=fastconv(arm(alpha,U)[::-1],arm(beta,V)[::-1])
        monomials_count,ranks=realization(q)
        algebra_cases+=1;basis_monomials+=monomials_count;power_map_ranks+=ranks
    out=dict(status='PASS',scope='Independent finite checks of the proved ordinary Hilbert/SLP realization and positive-difference O-sequence theorem. No general core unimodality claim.',
             seed=2026102097,ordinary_profiles_and_products=profiles,
             macaulay_degree_conditions=mac_tests,positive_difference_ratio_comparisons=ratio_tests,
             explicit_monomial_algebras=algebra_cases,basis_monomials=basis_monomials,
             exact_Lefschetz_power_map_rank_checks=power_map_ranks,
             seconds=time.monotonic()-start)
    ROOT.joinpath('audit_ordinary_lefschetz.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)

if __name__=='__main__':main()
