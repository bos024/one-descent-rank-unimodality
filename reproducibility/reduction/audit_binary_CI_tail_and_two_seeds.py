"""Exact identification/seed QA. The generic tail closure remains OPEN."""
from pathlib import Path
from math import comb
from random import Random
from collections import Counter
import hashlib,json,time
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_joint_structure import fastconv
from probe_ci_primitive_full_LC import window
from probe_binary_CI_two_seed_closure import binary
from audit_homogeneous_reference_and_sharp_entrance import rebuild


def main():
    start=time.monotonic();rng=Random(20261029071);counts=Counter();sha=hashlib.sha256()
    for case in range(2400):
        V=sorted(rng.choices(range(3,21),k=rng.randint(1,8)));h=sum(t-1 for t in V);r=len(V);W=h+r
        u=h+1 if case<1600 else rng.randint(1,h+12);m=u-1;alpha=rng.choice([1,2,3,4,u+h+1])
        M=alpha+2*u+W+1;F=arm_prefix(alpha,[2]*u+V,M);L=[1]
        for t in V:L=window(L,t)
        Cp=fastconv(L,binary(m));B=fastconv(L,[comb(u,j) for j in range(u+1)])
        def c(n):return (Cp[n] if 0<=n<len(Cp) else 0)-(B[n-m-alpha] if 0<=n-m-alpha<len(B) else 0)
        for n in range(h-1,M-r-1):
            actual=F[n+r+2]-F[n+r+1]
            assert actual==c(n),('tail product identity',V,u,alpha,n)
            counts['all_signed_actual_tail_coefficients_including_negative_tail']+=1
        if u==h+1:
            N0=W+3;ref=rebuild(V,W+6);rd=[1]+[ref[n]-ref[n-1] for n in range(1,len(ref))]
            b,cc,d,e=rd[W+1:W+5];A=cc**2-b*d;g=W+1;delta=2 if alpha==1 else 1
            eta=2*g+1 if alpha==1 else g+2 if alpha==2 else g+1
            assert F[N0]-F[N0-1]==d-delta
            assert F[N0+1]-F[N0]==e-eta
            assert A>0 and cc>=A and b<=cc and d==b+cc
            raw=c(m+1)**2-c(m)*c(m+2)
            assert raw==-A-2*delta*d+delta**2+cc*eta>=delta**2
            a=[max(0,c(j)) for j in range(m-1,m+3)]
            assert a[1]**2>a[0]*a[2] and a[2]**2>a[1]*a[3]
            counts['unbounded_seed_formula_instances_exact_QA']+=1
        sha.update(json.dumps([V,u,alpha,F],separators=(',',':')).encode())
        counts['actual_tail_contexts']+=1
    out=dict(status='PASS_EXACT_SIGNED_BINARY_CI_TAIL_IDENTITIES_AND_ENTIRE_TWO_SEED_FORMULAS',
        counts=dict(counts),sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='Written all-parameter identities and two strict entrance seeds, with three scoped Lean kernels. Generic two-seed LC closure remains OPEN; general C/A2/original UI remain OPEN.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
