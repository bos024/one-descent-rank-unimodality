"""Diagnostics of the next natural-crossing proof; not an original UI result."""
from pathlib import Path
from random import Random
from collections import Counter
from math import comb
import json,time,hashlib
from audit_binary_CI_infinite_padding_entrance import quotient,minor,convolution
from audit_arbitrary_Fibonacci_tail_late_C import add,sub,mul,sign
from audit_joint_structure import fastconv
from audit_degree_boundary_CI_entrance import ci
from verify_degree_boundary_CI_entrance import reverse_divided
from audit_padding_three_local_prefix import primitive,positive
ROOT=Path(__file__).resolve().parent
Q=(-1,1);Z=(0,0)

def main():
    started=time.monotonic();ct=Counter();bad={};sha=hashlib.sha256();rng=Random(20261029837)
    for u in range(32,151):
        qu=quotient(u)
        for s in range(2,u-1):
            for k in range(1,s+1):
                K=sub(mul(qu[s],qu[k]),mul(qu[s+1],qu[k-1]));T=add(add(qu[k+1],mul(mul((2,0),Q),qu[k])),mul(mul(Q,Q),qu[k-1]))
                M=sub(mul((5,0),K),mul((8,0),T));assert sign(M)>=0;ct['unscaled_eight_fifths_kernel_minors']+=1
    for _ in range(6000):
        # Integer triples, all LC/source comparisons are exact cross products.
        xm=rng.randint(1,100000);x=rng.randint(0,5*xm//3);xp=rng.randint(0,x*x//xm)
        em=rng.randint(0,2*xm);e=(10*em+2)//3+rng.randint(0,100000);ep=(10*e+2)//3+rng.randint(0,100000)
        A=[max(0,a-b) for a,b in zip((xm,x,xp),(em,e,ep))]
        assert A[1]**2>=A[0]*A[2];ct['generic_fast_source_clipped_LC_triples']+=1
        ct['generic_fast_source_all_three_positive']+=all(A)
        u=rng.randint(1,100);N=[rng.randint(0,1000) for _ in range(rng.randint(1,30))];E=fastconv([comb(u,j) for j in range(u+1)],N)
        for j in range(1,len(E)):
            assert j*E[j]>=(u-j+1)*E[j-1];ct['arbitrary_nonnegative_numerator_source_growth_edges']+=1
    for _ in range(1000):
        u=rng.randint(32,120);a=rng.randint(1,u//2);h=rng.randint(0,u-3)
        ratios=([a]+sorted([rng.randint(1,a) for _ in range(h-1)],reverse=True)) if h else []
        N=[1]
        for r in ratios:N.append(N[-1]*r)
        B=convolution(quotient(u),N)
        for s in range(2,u-1):
            T=add(add(B[s+1],mul(mul((2,0),Q),B[s])),mul(mul(Q,Q),B[s-1]))
            assert sign(sub(mul((5,0),minor(B,s)),mul((8,0),T)))>=0;ct['arbitrary_interval_supported_LC_unscaled_numerator_minors']+=1
        ct['generic_unscaled_LC_numerator_contexts']+=1
    for _ in range(4000):
        xm=rng.randint(100,100000);x=rng.randint(xm,5*xm//3);xp=rng.randint(x,x*x//xm)
        em=rng.randint(0,xm//100);e=(10*em+2)//3+rng.randint(0,x//100);ep=(10*e+2)//3+rng.randint(0,xp//100)
        A=[a-b for a,b in zip((xm,x,xp),(em,e,ep))]
        assert min(A)>0 and A[1]**2>=A[0]*A[2];ct['targeted_fast_source_all_three_strict_positive']+=1
    for _ in range(1600):
        u=rng.randint(16,200);ds=[];h=0
        while h<=u:
            d=rng.randint(3,max(3,u//rng.randint(2,6)));ds.append(d);h+=d
        while h-min(ds)>u:
            d=min(ds);ds.remove(d);h-=d
        V=sorted(d+1 for d in ds);J=reverse_divided(ci(V),u);start=h-u-1;b=J[start:];g=positive(primitive(b));ct['no_three_minimal_crossing_profiles']+=1
        for n,z in enumerate(b):
            if sign(z)<=0:bad.setdefault('natural_quotient_positive_tail',dict(u=u,V=V,start=start,n=n,value=z))
        for n in range(1,len(b)-1):
            z=minor(b,n);ct['natural_quotient_all_tail_minors']+=1
            if sign(z)<0:bad.setdefault('natural_quotient_first_or_later_minor',dict(u=u,V=V,start=start,n=n,value=z))
        for n in range(2,len(g)-1):
            z=minor(g,n);ct['natural_primitive_after_first_minors']+=1
            if sign(z)<0:bad.setdefault('natural_primitive_after_first_minor',dict(u=u,V=V,start=start,n=n,value=z))
        sha.update(json.dumps([u,V,b,g],separators=(',',':')).encode())
    out=dict(status='DIAGNOSTIC_ONLY_UNSCALED_HEAD_FAST_SOURCE_AND_NO_THREE_CROSSINGS',counts=dict(ct),counters=bad,
        state_sha256=sha.hexdigest(),seconds=time.monotonic()-started,
        scope='Written unbounded unscaled-head/fast-source arguments under audit; actual no-three quotient profiles are finite diagnostics. Natural source lag remains alpha-1. No general crossing theorem, C/A2 or original UI claim.')
    (ROOT/'probe_unscaled_head_and_fast_source.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)

if __name__=='__main__':main()
