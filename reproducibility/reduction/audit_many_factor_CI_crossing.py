"""New unbounded >=6-factor crossing route, pending written/formal audit."""
from pathlib import Path
from random import Random
from collections import Counter
import json,time,hashlib
from audit_degree_boundary_CI_entrance import ci
from verify_degree_boundary_CI_entrance import reverse_divided
from audit_arbitrary_Fibonacci_tail_late_C import add,sub,mul,power,sign
from audit_binary_CI_infinite_padding_entrance import quotient,minor,convolution
from audit_padding_three_local_prefix import primitive,positive
from audit_subdegree_CI_entrance import geometric_inverse
from audit_mode_only_uniform_tail_closure import tail
from audit_minimum_staircase_scaled_dyadic import arm_prefix
ROOT=Path(__file__).resolve().parent
Z=(0,0);Q=(-1,1);P=(0,1);PSI=(1,-1)

def main():
    start=time.monotonic();ct=Counter();sha=hashlib.sha256();seeds=[];cert=set();rng=Random(20261029851)
    for u,V in ((15,[4]*6),(16,[4]*5+[5]),(20,[5]*6)):
        h=sum(t-1 for t in V);clamp=(u+h)//2;row=dict(u=u,V=V,h=h,padding_clamp=clamp,hosts=[])
        for alpha in range(1,clamp+2):
            s=tail(V,u,alpha);g=[max(0,z) for z in s];M=g.index(max(g));margins=[]
            for n in range(1,M):
                z=g[n]**2-g[n-1]*g[n+1];assert z>=0;margins.append(z);cert.add(z);ct['complete_exception_minors']+=1
            row['hosts'].append(dict(alpha=alpha,first_tail_mode=M,margins=margins));ct['complete_exception_hosts']+=1
            sha.update(json.dumps([u,V,alpha,s],separators=(',',':')).encode())
        seeds.append(row)
    assert ct['complete_exception_hosts']==58
    for u in range(16,101):
        qu=quotient(u)
        for s in range(2,u-2):
            for k in range(1,s+1):
                K=sub(mul(qu[s],qu[k]),mul(qu[s+1],qu[k-1]));T=add(add(qu[k+1],mul(mul((2,0),Q),qu[k])),mul(mul(Q,Q),qu[k-1]))
                assert sign(sub(mul((4,0),K),mul((5,0),T)))>=0;ct['interior_five_fourths_unscaled_kernel_checks']+=1
            assert sign(sub(mul((12,0),qu[s]),(5*(4*u+5),0)))>=0;ct['unscaled_numerator_zero_row_checks']+=1
    for trial in range(700):
        r=rng.randint(6,14);V=sorted(rng.choices(range(4,20),k=r));h=sum(t-1 for t in V);delta=rng.randint(3,V[0]-1);u=h-delta
        assert u>=16 and h-min(t-1 for t in V)<=u and V[-1]<=u-11
        assert 13*(delta+1)<=3*(u+1)
        J=reverse_divided(ci(V),u);start_index=delta-1;b=J[start_index:];g=positive(primitive(b));ct['many_factor_minimal_crossing_profiles']+=1
        assert all(sign(z)>0 for z in b)
        for n in range(1,len(b)-1):assert sign(minor(b,n))>=0;ct['entire_natural_quotient_LC_minors']+=1
        for n in range(2,len(g)-1):assert sign(minor(g,n))>=0;ct['entire_natural_later_primitive_LC_minors']+=1
        X=geometric_inverse(J);W=sum(V)
        t=V[-1];B=convolution(quotient(u),ci(V[:-1]));a=mul(mul(P,P),sub((1,0),J[0]));signed=primitive(J)
        Y=[sub(B[n],mul(a,power(PSI,n))) for n in range(t+2)]
        gap=sub(mul(B[1],B[t-1]),mul((2,0),B[t]));assert sign(sub(mul((2,0),gap),(3*u,0)))>=0
        errcoef=mul(a,power(Q,t-1));errcoef=errcoef if sign(errcoef)>=0 else mul((-1,0),errcoef)
        assert sign(sub((1,0),mul((4,0),errcoef)))>=0;ct['unbounded_interval_junction_payments']+=1
        for alpha in {1,2,3,delta,rng.randint(1,u),u+delta+2}:
            F=arm_prefix(alpha,[2]*u+V,alpha+2*u+W+4);D=[max(0,F[n]-F[n-1]) if n else 1 for n in range(len(F))];M=D.index(max(D))
            for n in range(W+1,M):assert D[n]**2>=D[n-1]*D[n+1];ct['actual_all_padding_late_D_LC_minors']+=1
            st=tail(V,u,alpha)
            for s in range(min(len(st),len(F)-W)):
                assert st[s]==F[W+s]-F[W+s-1];ct['literal_actual_signed_tail_reads']+=1
            ct['actual_hosts']+=1
        sha.update(json.dumps([u,V,delta,b,g],separators=(',',':')).encode())
    out=dict(status='EXACT_QA_MANY_FACTOR_CROSSING_UNDER_PROOF_AUDIT',counts=dict(ct),
        complete_exception_profiles=seeds,integer_margins=sorted(cert),state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='Proposed UNBOUNDED actual late-D-LC for EVERY deletion-minimal crossing with >=6 CI factors; only THREE exceptional profiles are finite-certified. <=5-factor crossing entrance, general C/A2/original UI remain OPEN. Not registered.')
    (ROOT/'audit_many_factor_CI_crossing.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ('complete_exception_profiles','integer_margins')}),flush=True)
    print(json.dumps(dict(exception_profiles=len(seeds),integer_margins=len(cert))),flush=True)

if __name__=='__main__':main()
