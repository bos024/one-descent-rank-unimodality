"""Independent exact QA for the local-prefix alpha-three induction."""
from pathlib import Path
from math import comb
from random import Random
from collections import Counter
from itertools import accumulate
import hashlib,json,time
from audit_joint_structure import fastconv
from audit_arbitrary_Fibonacci_tail_late_C import add,sub,mul,power,sign,evaluate,absolute
from audit_binary_CI_infinite_padding_entrance import quotient,convolution,minor
from probe_divided_CI_positive_primitive import divided
from probe_finite_padding_geometric_deficit import arrays
from audit_minimum_staircase_scaled_dyadic import arm_prefix
Q=(-1,1);PHI=(0,1);PSI=(1,-1);ZERO=(0,0);ONE=(1,0)
P=[1,1,2,1];R=[1,2,3,3,1]

def scale(k,x):return mul((k,0),x)
def primitive(J):return [sub(v,J[n-1] if n else ZERO) for n,v in enumerate(J)]
def positive(d):return [x if sign(x)>0 else ZERO for x in d]
def parts(n,lo=2):
    yield []
    for k in range(lo,n+1):
        for rest in parts(n-k,k):yield [k]+rest

def main():
    start=time.monotonic();rng=Random(20261029752);ct=Counter();sha=hashlib.sha256();small=[];cert=set()
    for u in range(1,8):
        for p in parts(u-1):
            L=[1]
            for x in p:L=fastconv(L,[1]*(x+1))
            E,J=divided(fastconv(L,P),u);d=primitive(J);dp=positive(d);K=u-2
            for n in range(max(0,K+2)):
                assert sign(J[n])>0;cert.add(sub(scale(100,J[n]),ONE))
                ct['complete_small_positive_read_coefficients']+=1
            for n in range(1,K+1):
                assert sign(minor(J,n))>=0 and sign(minor(dp,n))>=0
                cert.add(minor(J,n));cert.add(minor(dp,n))
                ct['complete_small_both_prefix_minors']+=1
            assert not any(sign(d[j])>0 for j in range(next((n for n,x in enumerate(d[:max(0,K+2)]) if sign(x)<=0),max(0,K+2)),max(0,K+2)))
            small.append(dict(u=u,degree_partition=p,J=J,positive_primitive=dp))
    assert len(small)==30
    E,J=divided(P,8);dp=positive(primitive(J))
    for x in J:cert.add(sub(scale(100,x),ONE));assert sign(x)>0
    for n in range(1,len(J)-1):
        assert sign(minor(J,n))>=0 and sign(minor(dp,n))>=0
        cert.add(minor(J,n));cert.add(minor(dp,n));ct['complete_binary_eight_full_support_minors']+=1
    cert=sorted(cert)
    for a,b in cert:
        assert 1000000*a+b*(1618033 if b>=0 else 1618034)>=0,(a,b)
    for u in range(8,151):
        E,J=divided(P,u);c=evaluate(E,(0,-1));d=primitive(J);w=u+1;a=E[2];b=E[3]
        assert a==(u*u+u+4)//2 and b==(u**3+11*u+6)//6
        H=a*w+a-w*w-b
        M20=(a*a+a-w*b-w,-H);AA=(w-a,a-b)
        assert minor(d,2)==add(M20,mul(c,AA))
        assert H>=0 and sign(AA)<=0 and sign(add(AA,(2*b,0)))>=0
        assert sign(sub(scale(36,minor(d,2)),(3*u**4-14*u**3-3*u*u-10*u-12,0)))>=0
        ct['exact_padding_three_binary_second_heads']+=1
        for n in range(1,len(J)-1):
            assert sign(minor(J,n))>=0 and sign(minor(positive(d),n))>=0
            ct['exact_padding_three_binary_entire_ordinary_and_primitive_minors']+=1
        sha.update(json.dumps([u,J,d],separators=(',',':')).encode())
    # Arbitrary LC numerators, including degree ABOVE the binomial parameter.
    for trial in range(1000):
        v=rng.randint(7,60);a=rng.randint(1,(v+3)//2);degree=rng.randint(1,2*v)
        N=[1];ratio=a
        for n in range(degree):
            if n and rng.random()<.25:ratio=max(1,ratio-1)
            N.append(N[-1]*ratio)
        BB=convolution(quotient(v),N)
        for s in range(1,v):
            T=add(add(BB[s+1],scale(2,mul(Q,BB[s]))),mul(power(Q,2),BB[s-1]))
            assert sign(sub(minor(BB,s),mul(power(Q,s),T)))>=0,('relaxed robust',v,a,s)
            ct['exact_relaxed_generic_robust_all_prefix_minors']+=1
        ct['generic_LC_numerators_with_relaxed_budget']+=1
    for trial in range(1200):
        Vold=rng.choices(range(3,25),k=rng.randint(0,7));t=rng.randint(3,27)
        V=Vold+[t];h=sum(x-1 for x in V);u=max(8,h+1+rng.randint(0,8));r=len(Vold);K=u-2
        L0=[1]
        for x in Vold:L0=fastconv(L0,[1]*x)
        L=fastconv(L0,[1]*t);E,J=divided(fastconv(L,P),u);c=evaluate(E,(0,-1));d=primitive(J)
        _,Jo=divided(fastconv(L0,P),u);win=convolution(Jo,[1]*t)
        _,Jt=divided([1]*t,0);co=evaluate(fastconv(fastconv(L0,P),[comb(u,j) for j in range(u+1)]),(0,-1))
        corr=[mul(co,x) for x in Jt]+[ZERO]*(len(J)-len(Jt))
        assert all(sub(x,y)==z for x,y,z in zip(J,win,corr))
        for n in range(t,len(J)):assert d[n]==primitive(win)[n]
        ct['exact_padding_three_append_quotient_identities']+=1
        B=convolution(quotient(u),fastconv(L0,P));B_alt=convolution(quotient(u-1),fastconv(L0,R))
        assert B[:u]==B_alt[:u]
        aa=mul(mul(PHI,PHI),c);X=[sub(B[n],mul(aa,power(PSI,n))) for n in range(u)]
        assert all(sign(x)>0 for x in X)
        for n in range(1,u-1):
            assert sign(minor(X,n))>=0
            ct['exact_padding_three_robust_X_head_minors']+=1
        for n in range(1,min(t,u)):assert d[n]==X[n]
        if t<u:assert d[t]==sub(X[t],ONE)
        if t+1<u:assert d[t+1]==sub(X[t+1],B[1])
        D=sub(mul(B[1],B[1]),scale(2,B[2]))
        assert D==sub((u-r-3,0),mul(Q,Q))
        assert B[1]==add((u+r,0),mul(Q,Q))
        if t<=K:
            assert sign(sub(B[t-1],scale(r+2,sub((u,0),Q))))>=0
            gap=sub(mul(B[1],B[t-1]),scale(2,B[t]))
            assert sign(sub(scale(2,gap),(u,0)))>=0
            gapx=sub(mul(B[1],X[t-1]),scale(2,X[t]))
            assert sign(sub(scale(6,gapx),(u,0)))>=0
            assert minor(d,t)==add(add(minor(X,t),gapx),ONE)
            assert sign(sub(scale(6,minor(d,t)),(6+u,0)))>=0
            ct['exact_padding_three_junction_lower_bounds']+=1
        w=u+len(V)+1
        assert E[0]==1 and E[1]==w and 2*E[2]==w*w-u+len(V)+3
        assert 2*E[2]<=w*w and sign(sub(scale(2,minor(d,1)),(3,0)))>=0
        for n in range(u):assert sign(J[n])>0
        for n in range(1,K+1):
            assert sign(minor(J,n))>=0 and sign(minor(positive(d),n))>=0,('prefix',V,u,n)
            ct['exact_padding_three_both_local_prefix_minors']+=1
        # Local closure sees only the truncated prefix, not its later shape.
        trunc=Jo[:K+2];wtrunc=convolution(trunc,[1]*t)
        assert wtrunc[:K+2]==win[:K+2]
        for n in range(1,K+1):
            assert sign(minor(wtrunc,n))>=0 and sign(minor(positive(primitive(wtrunc)),n))>=0
            ct['exact_local_prefix_truncation_window_minors']+=1
        ct['padding_three_CI_induction_contexts']+=1
        sha.update(json.dumps([V,u,J,d,X],separators=(',',':')).encode())
        if trial%3==0:
            m=h;actualu=m+1;V=sorted(V);rr=len(V);W=h+rr
            _,entryJ=divided(fastconv(L,P),actualu);entryd=primitive(entryJ)
            _,_,_,raw,Aseq,_=arrays(V,m,3);ell=Aseq.index(max(Aseq))
            rawb=[sub((0,raw[n-1] if n else 0),(raw[n],0)) for n in range(len(raw))]
            for s in range(1,actualu+1):assert rawb[actualu+s]==entryd[s];ct['exact_padding_three_actual_head_identities']+=1
            for n in range(m,ell+1):assert Aseq[n]**2>=Aseq[n-1]*Aseq[n+1];ct['exact_padding_three_actual_through_first_mode_LC_minors']+=1
            T=2*actualu+W;F=arm_prefix(3,[2]*actualu+V,T+5);G=list(accumulate(F))
            Dact=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];best=1
            for N in range(4,T+2):
                k=N-3
                if G[k]*G[best-1]<G[best]*G[k-1]:best=k
                if N>=W+1:assert G[best]*Dact[N-1]>=G[best-1]*Dact[N];ct['exact_padding_three_all_read_prefix_minimum_C_payments']+=1
            ct['actual_padding_three_entry_contexts']+=1
    out=dict(status='PASS_EXACT_QA_LOCAL_CI_PREFIX_AND_ACTUAL_PADDING_THREE',counts=dict(ct),
        small_contexts=small,small_scalar_certificate=cert,small_scalar_certificate_count=len(cert),
        state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='Exact finite QA ONLY. Universal proof is the separately written relaxed robust estimate and local simultaneous interval induction, with COMPLETE degree<=6 exceptions. No general remaining alpha4..h, early reference C, shorter counts, C/A2/original UI conclusion.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['small_contexts','small_scalar_certificate']}),flush=True)

if __name__=='__main__':main()
