"""Exact audit of the NEW degree-boundary refinement; not an exhaustive general proof."""
from pathlib import Path
from collections import Counter
from itertools import accumulate
from random import Random
from math import comb
import hashlib,json,time
from audit_joint_structure import fastconv
from audit_arbitrary_Fibonacci_tail_late_C import add,sub,mul,power,sign
from audit_binary_CI_infinite_padding_entrance import quotient,minor,convolution
from probe_divided_CI_positive_primitive import divided
from audit_padding_three_local_prefix import primitive,positive
from probe_finite_padding_geometric_deficit import arrays
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import rebuild

ROOT=Path(__file__).resolve().parent
Q=(-1,1);P=(0,1);PSI=(1,-1);ZERO=(0,0)
LO=16180339887498948;HI=16180339887498949;DEN=10**16

def partitions(n,lo=2):
    if n==0:yield []
    for d in range(lo,n+1):
        for tail in partitions(n-d,d):yield [d]+tail

def scalar(x):return (x,0)
def ci(V):
    L=[1]
    for t in V:L=fastconv(L,[1]*t)
    return L

def main():
    start=time.monotonic();ct=Counter();sha=hashlib.sha256();cert=set();small=[];startup=[];integers=set()
    controlF=arm_prefix(2,[2]*4+[3,3],15)
    controlD=[0,0]+[max(0,controlF[n]-controlF[n-1]) for n in range(2,len(controlF))]
    assert controlD[6:9]==[8,12,19] and controlD[7]**2-controlD[6]*controlD[8]==-8
    def pay(x,label,certify=False):
        assert sign(x)>=0,(label,x)
        ct[label]+=1
        if certify:cert.add(x)
    for u in range(2,16):
        for ds in partitions(u):
            V=[d+1 for d in ds];E,J=divided(ci(V),u);dp=positive(primitive(J))
            exception=(V==[4])
            for x in J:
                assert sign(x)>0
                pay(x,'complete_small_positive_entries',True)
            for n in range(1,len(J)-1):pay(minor(J,n),'complete_small_ordinary_minors',True)
            for n in range(2,len(dp)-1):
                if exception:
                    if n==2:assert minor(dp,n)==(3,-2) and sign(minor(dp,n))<0
                    else:pay(minor(dp,n),'excluded_context_other_primitive_minors')
                else:pay(minor(dp,n),'complete_small_later_primitive_minors',True)
            small.append(dict(u=u,V=V,exception=exception))
            sha.update(json.dumps([u,V,J,dp],separators=(',',':')).encode())
            if u+len(V)<8:
                for alpha in range(1,u+1):
                    _,C,E,raw,A,_=arrays(V,u-1,alpha);ell=A.index(max(A));margins=[]
                    for n in range(u-1,ell):
                        M=A[n]**2-A[n-1]*A[n+1];assert M>=0
                        integers.add(M);margins.append(M);ct['complete_small_startup_coefficient_minors']+=1
                    # Infinite-padding last centre, independently of any primitive theorem.
                    for n in range(u-1,len(C)-1):assert C[n]**2>=C[n-1]*C[n+1]
                    startup.append(dict(u=u,V=V,alpha=alpha,first_mode=ell,margins=margins))
    assert len(small)==175 and sum(x['exception'] for x in small)==1 and len(startup)==29
    for a,b in cert:
        assert DEN*a+b*(LO if b>=0 else HI)>=0,('fine_root_certificate',a,b)
    for u in range(16,76):
        QU=quotient(u)
        def at(k):return QU[k] if 0<=k<len(QU) else ZERO
        T=[add(add(at(k+1),mul(mul((2,0),Q),at(k))),mul(power(Q,2),at(k-1))) for k in range(u)]
        for s in range(2,u):
            factor=mul((4,0),power(Q,s))
            pay(sub(QU[s],mul(power(Q,s),add((6*u,0),mul((4,0),Q)))),'quadruple_row_zero')
            for k in range(1,s+1):
                K=sub(mul(QU[s],QU[k]),mul(QU[s+1],QU[k-1]))
                pay(sub(K,mul(factor,T[k])),'quadruple_all_rows_including_last')
        pay(sub((1,0),mul((3*u*(u+1),0),power(Q,u-1))),'quadratic_geometric_power')
    rng=Random(20261029763)
    for trial in range(500):
        u=rng.randint(16,65);r=rng.randint(0,u//2);V=rng.choices(range(3,24),k=r)
        N=ci(V);B=convolution(quotient(u),N)
        for s in range(2,u):
            T=add(add(B[s+1],mul(mul((2,0),Q),B[s])),mul(power(Q,2),B[s-1]))
            pay(sub(minor(B,s),mul(mul((4,0),power(Q,s)),T)),'generic_arbitrary_degree_quadruple_head')
        ct['generic_LC_numerator_contexts']+=1
    for trial in range(900):
        V=sorted(rng.choices(range(3,26),k=rng.randint(1,8)));u=sum(t-1 for t in V);L=ci(V)
        E,J=divided(L,u);c=sub((1,0),J[0]);assert sign(c)>0 and sign(sub((1,0),c))>0
        for x in J:assert sign(x)>0;ct['boundary_ordinary_positive_entries']+=1
        for n in range(1,len(J)-1):pay(minor(J,n),'boundary_entire_ordinary_minors')
        dp=positive(primitive(J))
        if V!=[4]:
            for n in range(2,len(dp)-1):pay(minor(dp,n),'boundary_entire_later_primitive_minors')
        _,C,_,_,_,_=arrays(V,u-1,1)
        assert sub(mul(P,(C[u-2],0)),(C[u-1],0))==mul((-1,0),mul(P,sub((1,0),c)))
        ct['exact_initial_geometric_inverse_boundary']+=1
        for n in range(u-1,len(C)-1):
            assert C[n]**2>=C[n-1]*C[n+1];ct['infinite_boundary_coefficient_minors']+=1
        if len(V)==1 and u>=3:
            d=primitive(J);pp=power(PSI,u)
            expected=[sub(sub(mul(P,(u,0)),power(P,2)),mul(power(P,3),pp)),
                add(P,mul(power(P,2),pp)),mul((-1,0),mul(P,pp)),sub(pp,(1,0))]
            assert d[u-2:u+2]==expected
            if u%2 and u>=5:assert minor(d,u-1)==mul(power(P,2),sub((1,0),mul(add((u,0),P),power(Q,u))))
            ct['single_interval_exact_endpoints']+=1
        elif len(V)>=2:
            t=V[-1];old=V[:-1];r=len(old);B=convolution(quotient(u),ci(old));a=mul(power(P,2),c)
            X=[sub(B[n] if n<len(B) else ZERO,mul(a,power(PSI,n))) for n in range(u+1)]
            b=B[1];gap=sub(mul(b,X[t-1]),mul((2,0),X[t]))
            if u>=16:pay(sub(mul((25,0),gap),(u,0)),'nonempty_boundary_junction_gap')
            d=primitive(J)
            for n in range(1,t):assert d[n]==X[n]
            assert d[t]==sub(X[t],(1,0)) and d[t+1]==sub(X[t+1],b)
            ct['exact_new_interval_primitive_identity']+=1
        W=u+len(V);ref=rebuild(V,2*u+W+3);rd=[1]+[ref[n]-ref[n-1] for n in range(1,len(ref))]
        assert sub((rd[W+2],0),mul(P,(rd[W+1],0)))==c
        ct['exact_first_actual_defect_subgolden_join']+=1
        for alpha in {1,2,rng.randint(1,u),u+1,u+8}:
            _,C,E,raw,A,_=arrays(V,u-1,alpha);ell=A.index(max(A))
            for n in range(u-1,ell):
                assert A[n]**2>=A[n-1]*A[n+1];ct['all_padding_boundary_coefficient_minors']+=1
            F=arm_prefix(alpha,[2]*u+V,2*u+W+2);D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];G=list(accumulate(F));best=1
            for n in range(4,len(F)):
                k=n-3
                if G[k]*G[best-1]<G[best]*G[k-1]:best=k
                if n>=W+1:
                    assert G[best]*D[n-1]>=G[best-1]*D[n],('lateC',V,u,alpha,n,best)
                    ct['actual_boundary_all_read_minimum_C']+=1
            if u>=3:
                assert D[W]==A[u-2]+1 and D[W+1]==A[u-1] and D[W+1]>D[W]
                assert D.index(max(D))==len(V)+2+ell
                ct['strict_actual_boundary_mode_identification']+=1
            for n in range(u-1,min(len(A),len(D)-len(V)-2)):
                assert D[len(V)+2+n]==A[n]
                ct['literal_actual_signed_tail_identification']+=1
            sha.update(json.dumps([V,u,alpha,C,A,F,D],separators=(',',':')).encode())
            ct['boundary_actual_contexts']+=1
    out=dict(status='EXACT_QA_PASS_DEGREE_BOUNDARY_REFINEMENT_UNDER_PROOF_AUDIT',counts=dict(ct),
        complete_small_contexts=small,complete_small_startup_contexts=startup,
        complete_small_scalar_margins=sorted(cert),complete_small_startup_integer_margins=sorted(integers),
        rational_root_interval=dict(lower=LO,upper=HI,denominator=DEN),
        negative_control=dict(V=[4],u=3,primitive_centre=2,margin=[3,-2]),
        actual_earlier_LC_negative_control=dict(V=[3,3],u=4,alpha=2,centre=7,triple=[8,12,19],margin=-8),
        state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='Finite QA of a separately written unbounded refinement. General C/A2/original UI remain OPEN. No finite test is substituted for the analytic induction; formal and independent generation audits are pending.')
    (ROOT/'audit_degree_boundary_CI_entrance.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if not k.startswith('complete_small')},ensure_ascii=False),flush=True)
    print(json.dumps(dict(complete_small_contexts=len(small),distinct_field_margins=len(cert),complete_small_startups=len(startup),distinct_integer_margins=len(integers))),flush=True)

if __name__=='__main__':main()
