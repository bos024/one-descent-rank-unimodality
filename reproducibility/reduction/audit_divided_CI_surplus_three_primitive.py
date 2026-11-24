"""Independent exact QA of every junction in the surplus-three primitive theorem."""
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


def scale(k,x):return mul((k,0),x)


def primitive(J):
    return [sub(v,J[n-1] if n else ZERO) for n,v in enumerate(J)]


def main():
    started=time.monotonic();rng=Random(20261029745);ct=Counter();sha=hashlib.sha256()
    for U in range(3,151):
        E,R=divided([1],U);c=power(PSI,U);d=primitive(R)
        A=comb(U,2);C=comb(U,3)
        expected=[sub(ONE,c),add(sub((U,0),PHI),mul(PHI,c)),
            sub(add(sub((A,0),scale(U,PHI)),ONE),c),
            add(sub(add(sub((C,0),scale(A,PHI)),(U,0)),Q),mul(Q,c))]
        assert d[:min(4,len(d))]==expected[:min(4,len(d))]
        if U>=4:
            M1=add(add(sub((U*(U+1)//2,0),scale(U-1,PHI)),
                mul(c,add((A,0),scale(U-2,PHI)))),mul(PHI,mul(c,c)))
            assert minor(d,1)==M1
            assert sign(sub(scale(12,M1),(5*U*U-21*U+32,0)))>=0
            ct['exact_binary_first_head_payments']+=1
        if U>=6:
            M2=add(sub((U*(U**3+5*U-18)//12,0),
                      scale(U*(2*U-5)*(U+1)//6,PHI)),
                    mul(c,sub(add(scale(A,Q),(U,0)),scale(C,PHI))))
            # The rational polynomial numerator is divisible by twelve
            # in this expression; keep the equality independently checked.
            assert minor(d,2)==M2
            lower=U*(3*U**3-26*U*U+57*U+2)
            assert sign(sub(scale(36,M2),(lower,0)))>=0
            ct['exact_binary_second_head_payments']+=1
        if U in [3,4,5]:
            assert sign(d[2] if U==3 else d[3])<=0
            ct['exact_small_binary_primitive_bases']+=1
        dp=[x if sign(x)>0 else ZERO for x in d]
        for n in range(1,len(dp)-1):
            assert sign(minor(dp,n))>=0,('binary primitive',U,n)
            ct['exact_entire_binary_positive_primitive_minors']+=1
        if U>=4:
            _,old=divided([1],U-1);window=convolution(old,[1,1]);eps=mul(PHI,power(PSI,U-1))
            window[0]=add(window[0],eps)
            assert window==R
            ct['exact_binary_constant_update_identities']+=1
        sha.update(json.dumps([U,R,dp],separators=(',',':')).encode())
    for trial in range(1200):
        Vold=rng.choices(range(3,23),k=rng.randint(0,6));t=rng.randint(3,25)
        V=Vold+[t];h=sum(v-1 for v in V);U=h+3+rng.randint(0,8);r=len(Vold)
        L0=[1]
        for v in Vold:L0=fastconv(L0,[1]*v)
        L=fastconv(L0,[1]*t);E,J=divided(L,U);c=evaluate(E,(0,-1));d=primitive(J)
        _,Jold=divided(L0,U);base=convolution(Jold,[1]*t)
        _,Jt=divided([1]*t,0);c0=mul(power(PSI,U),evaluate(L0,(0,-1)))
        correction=[mul(c0,x) for x in Jt]+[ZERO]*(len(J)-len(Jt))
        assert len(base)==len(J) and all(sub(x,y)==z for x,y,z in zip(J,base,correction))
        ct['exact_entire_interval_append_quotient_identities']+=1
        B=convolution(quotient(U),L0);a=mul(mul(PHI,PHI),c)
        assert sign(sub(scale(4,power(Q,3)),scale(5,absolute(c))))>=0
        assert sign(sub(scale(4,Q),scale(5,absolute(a))))>=0
        X=[sub(B[n],mul(a,power(PSI,n))) for n in range(U)]
        assert all(sign(x)>0 for x in X)
        for n in range(1,t):assert d[n]==X[n]
        assert d[t]==sub(X[t],ONE) and d[t+1]==sub(X[t+1],B[1])
        ct['exact_all_low_primitive_source_identities']+=t+1
        for n in range(1,U-1):
            assert sign(minor(X,n))>=0
            ct['exact_robust_head_X_minors']+=1
        D=sub(mul(B[1],B[1]),scale(2,B[2]))
        assert D==sub((U-r,0),mul(Q,Q))
        gap=sub(mul(B[1],B[t-1]),scale(2,B[t]))
        assert sign(sub(scale(3,gap),(U,0)))>=0
        gapX=sub(mul(B[1],X[t-1]),scale(2,X[t]))
        assert sign(sub(scale(30,gapX),(U,0)))>=0
        assert minor(d,t)==add(add(minor(X,t),gapX),ONE)
        assert sign(sub(scale(30,minor(d,t)),(30+U,0)))>=0
        ct['exact_quantitative_last_junction_payments']+=1
        w=U+len(V);E2=E[2]
        expected=add(add(sub((w*w-E2,0),scale(w-1,PHI)),
                        mul(c,add((E2,0),scale(w-2,PHI)))),mul(PHI,mul(c,c)))
        assert minor(d,1)==expected
        assert sign(sub(scale(2,expected),(3,0)))>=0
        ct['exact_actual_first_primitive_seed_payments']+=1
        dp=[v if sign(v)>0 else ZERO for v in d]
        for n in range(1,len(dp)-1):
            assert sign(minor(dp,n))>=0,('entire CI primitive',V,U,n)
            ct['exact_entire_divided_CI_positive_primitive_minors']+=1
        ct['independent_CI_interval_induction_contexts']+=1
        sha.update(json.dumps([V,U,J,d,X],separators=(',',':')).encode())
        if trial%3==0:
            m=U-3;u=m+1;V=sorted(V);rr=len(V);W=h+rr
            LL,Cinf,EE,raw,Aseq,b=arrays(V,m,2);ell=Aseq.index(max(Aseq))
            rawb=[sub((0,raw[n-1] if n else 0),(raw[n],0)) for n in range(len(raw))]
            for s in range(1,u+1):
                assert rawb[u+s]==d[s]
                ct['exact_padding_two_divided_primitive_head_identities']+=1
            for n in range(m,ell+1):
                assert Aseq[n]**2>=Aseq[n-1]*Aseq[n+1]
                ct['exact_actual_padding_two_through_first_mode_LC_minors']+=1
            T=2*u+W;F=arm_prefix(2,[2]*u+V,T+5);G=list(accumulate(F))
            Dact=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
            best=1
            for N in range(4,T+2):
                k=N-3
                if G[k]*G[best-1]<G[best]*G[k-1]:best=k
                if N>=W+1:
                    assert G[best]*Dact[N-1]>=G[best-1]*Dact[N]
                    ct['exact_actual_padding_two_all_read_prefix_minimum_C_payments']+=1
            ct['actual_padding_two_contexts']+=1
    out=dict(status='PASS_EXACT_QA_SURPLUS_THREE_PRIMITIVE_AND_ACTUAL_PADDING_TWO_ENTRANCE',
        counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-started,
        scope='Exact finite independent QA of every specified head/junction identity in the WRITTEN unbounded induction and its actual padding-two corollary. The proof uses unbounded induction, not this finite search as a universal entrance. No arbitrary-padding/general C/A2/original UI conclusion.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
