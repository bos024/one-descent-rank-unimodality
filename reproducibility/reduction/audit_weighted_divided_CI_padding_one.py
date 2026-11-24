"""Independent exact QA of the weighted divided-CI prefix and actual padding one."""
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
def primitive(J):return [sub(v,J[n-1] if n else ZERO) for n,v in enumerate(J)]
def positive(d):return [x if sign(x)>0 else ZERO for x in d]

def main():
    started=time.monotonic();rng=Random(20261029747);ct=Counter();sha=hashlib.sha256()
    for u in range(1,151):
        E,J=divided([2,1],u);c=evaluate(E,(0,-1));d=primitive(J)
        assert c==mul(power(Q,2),power(PSI,u))
        if u==1:assert J==[(-1,2),(0,1)] and sign(d[1])<0
        if u in [2,3]:assert sign(d[2])<=0
        if u in [4,5]:assert sign(d[3])<=0
        if u<=5:ct['exact_small_weighted_binary_bases']+=1
        if u>=2:
            M=add(add(sub((2*u*u+4*u+1,0),scale(4*u-2,PHI)),
                mul(c,add((u*u,0),scale(2*u-3,PHI)))),mul(PHI,mul(c,c)))
            assert minor(d,1)==M
            assert sign(sub(scale(6,M),(11*u*u-28*u+36,0)))>=0
            assert sign(sub(M,(4,0)))>=0
            ct['exact_weighted_binary_first_head_payments']+=1
            _,old=divided([2,1],u-1);window=convolution(old,[1,1])
            window[0]=add(window[0],mul(PHI,mul(power(Q,2),power(PSI,u-1))))
            assert window==J
            ct['exact_weighted_binary_constant_update_identities']+=1
        if u>=6:
            M20times6=(2*u**4+4*u**3+13*u*u-25*u-12,-8*u**3+26*u+6)
            Atimes6=(6+12*u-6*u*u,-u+9*u*u-2*u**3)
            assert scale(6,minor(d,2))==add(M20times6,mul(c,Atimes6))
            assert sign(Atimes6)<=0 and sign(add(Atimes6,(4*u**3,0)))>=0
            assert sign(sub(scale(18,minor(d,2)),(u*(6*u**3-38*u*u+39*u+81),0)))>=0
            ct['exact_weighted_binary_second_head_payments']+=1
        dp=positive(d)
        for n in range(1,len(dp)-1):
            assert sign(minor(dp,n))>=0,('binary primitive',u,n)
            ct['exact_entire_weighted_binary_positive_primitive_minors']+=1
        sha.update(json.dumps([u,J,dp],separators=(',',':')).encode())
    for trial in range(1200):
        Vold=rng.choices(range(3,23),k=rng.randint(0,6));t=rng.randint(3,25)
        V=Vold+[t];h=sum(v-1 for v in V);u=h+1+rng.randint(0,8);r=len(Vold)
        L0=[1]
        for v in Vold:L0=fastconv(L0,[1]*v)
        L=fastconv(L0,[1]*t);weighted=fastconv(L,[2,1])
        E,J=divided(weighted,u);c=evaluate(E,(0,-1));d=primitive(J);K=u-2
        _,unweighted=divided(L,u);cc=mul(power(PSI,u),evaluate(L,(0,-1)))
        JJ=convolution(unweighted,[2,1]);JJ[0]=add(JJ[0],mul(PHI,cc))
        assert JJ==J and c==mul(power(Q,2),cc)
        v=u+len(V);w=2*v+1;E2=v*v+2*len(V)
        assert E[:3]==[2,w,E2] and J[0]==sub((2,0),c)
        ordinary=sub((w*w,0),mul(sub((2,0),c),add((E2,0),scale(w,Q))))
        assert minor(J,1)==ordinary
        assert sign(sub(scale(5,ordinary),(9*v*v-2*v+5,0)))>=0
        for n in range(1,len(J)-1):
            assert sign(minor(J,n))>=0
            ct['exact_entire_weighted_CI_ordinary_LC_minors']+=1
        assert all(sign(x)>0 for x in J)
        ct['exact_weighted_ordinary_first_head_payments']+=1
        _,Jold=divided(fastconv(L0,[2,1]),u);base=convolution(Jold,[1]*t)
        _,Jt=divided([1]*t,0);c0=evaluate(fastconv(fastconv(L0,[2,1]),[comb(u,j) for j in range(u+1)]),(0,-1))
        correction=[mul(c0,x) for x in Jt]+[ZERO]*(len(J)-len(Jt))
        assert len(base)==len(J) and all(sub(x,y)==z for x,y,z in zip(J,base,correction))
        for n in range(t,len(J)):assert d[n]==primitive(base)[n]
        ct['exact_weighted_interval_append_quotient_identities']+=1
        B=convolution(quotient(u),fastconv(L0,[2,1]));a=mul(mul(PHI,PHI),c)
        assert sign(sub(scale(4,power(Q,3)),scale(5,absolute(c))))>=0
        assert sign(sub(scale(4,Q),scale(5,absolute(a))))>=0
        X=[sub(B[n],mul(a,power(PSI,n))) for n in range(u)]
        assert all(sign(x)>0 for x in X)
        for n in range(1,min(t,u)):assert d[n]==X[n]
        if t<u:assert d[t]==sub(X[t],(2,0))
        if t+1<u:assert d[t+1]==sub(X[t+1],B[1])
        ct['exact_weighted_low_primitive_source_identities']+=min(t+1,u-1)
        for n in range(1,u-1):
            assert sign(minor(X,n))>=0
            ct['exact_weighted_robust_X_head_minors']+=1
        D=sub(mul(B[1],B[1]),scale(4,B[2]))
        assert D==add(scale(4,sub((u-r,0),mul(Q,Q))),ONE)
        if t<=K:
            gap=sub(mul(B[1],B[t-1]),scale(4,B[t]))
            assert sign(sub(scale(3,gap),(4*u,0)))>=0
            gapX=sub(mul(B[1],X[t-1]),scale(4,X[t]))
            assert sign(sub(scale(15,gapX),(11*u,0)))>=0
            assert minor(d,t)==add(add(minor(X,t),gapX),(4,0))
            assert sign(sub(scale(15,minor(d,t)),(60+11*u,0)))>=0
            ct['exact_weighted_quantitative_last_junction_payments']+=1
        expected=add(add(sub((w*w-2*E2,0),scale(2*(w-2),PHI)),
                mul(c,add((E2,0),scale(w-4,PHI)))),mul(PHI,mul(c,c)))
        assert minor(d,1)==expected
        assert sign(sub(scale(5,expected),(57,0)))>=0
        ct['exact_weighted_actual_first_primitive_payments']+=1
        dp=positive(d)
        for n in range(1,K+1):
            assert sign(minor(dp,n))>=0,('weighted CI prefix',V,u,n)
            ct['exact_weighted_CI_positive_primitive_prefix_minors']+=1
        # Exercise the prefix-window lemma at ALL possible clipping positions.
        d0=positive(primitive(Jold));m=next((n for n in range(len(Jold)-1) if sign(sub(Jold[n+1],Jold[n]))<=0),len(Jold)-1)
        dpbase=positive(primitive(base))
        for k in sorted({0,1,max(0,m-1),m,m+1,K}):
            if all(sign(minor(d0,n))>=0 for n in range(1,min(k,len(d0)-2)+1)):
                for n in range(1,min(k,len(dpbase)-2)+1):
                    assert sign(minor(dpbase,n))>=0
                    ct['exact_prefix_window_boundary_minors']+=1
        ct['weighted_CI_induction_contexts']+=1
        sha.update(json.dumps([V,u,J,d,X],separators=(',',':')).encode())
        if trial%3==0:
            # Entry m=h, not a larger m substituted for the single entry.
            m=h;actualu=m+1;V=sorted(V);rr=len(V);W=h+rr
            _,entryJ=divided(weighted,actualu);entryd=primitive(entryJ)
            LL,Cinf,EE,raw,Aseq,b=arrays(V,m,1);ell=Aseq.index(max(Aseq))
            rawb=[sub((0,raw[n-1] if n else 0),(raw[n],0)) for n in range(len(raw))]
            for s in range(1,actualu+1):
                assert rawb[actualu+s]==entryd[s]
                ct['exact_padding_one_primitive_head_identities']+=1
            for n in range(m,ell+1):
                assert Aseq[n]**2>=Aseq[n-1]*Aseq[n+1]
                ct['exact_actual_padding_one_through_first_mode_LC_minors']+=1
            T=2*actualu+W;F=arm_prefix(1,[2]*actualu+V,T+5);G=list(accumulate(F))
            Dact=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
            best=1
            for N in range(4,T+2):
                k=N-3
                if G[k]*G[best-1]<G[best]*G[k-1]:best=k
                if N>=W+1:
                    assert G[best]*Dact[N-1]>=G[best-1]*Dact[N]
                    ct['exact_padding_one_all_read_prefix_minimum_C_payments']+=1
            ct['actual_padding_one_entry_contexts']+=1
    # A fixed control rules out extending arbitrary-padding head LC after the mode.
    _,_,_,raw,A,b=arrays([4,32],34,19)
    assert A.index(max(A))==61 and minor(b,63)==(92474729448806994408,-59412110474266913988)
    assert sign(minor(b,63))<0
    out=dict(status='PASS_EXACT_QA_WEIGHTED_CI_PREFIX_AND_ACTUAL_PADDING_ONE_ENTRANCE',counts=dict(ct),
        state_sha256=sha.hexdigest(),seconds=time.monotonic()-started,
        postmode_negative_control=dict(V=[4,32],m=34,alpha=19,first_A_mode=61,n=63,minor=list(minor(b,63))),
        scope='Exact finite QA only of the WRITTEN all-degree weighted prefix induction and actual alpha1 corollary. Prefix is through u-2, NOT a general arbitrary-padding full-tail assertion. No general C/A2/original UI conclusion.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)

if __name__=='__main__':main()
