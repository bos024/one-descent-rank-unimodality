"""Finite diagnostic of OPEN short-padding clipped-deficit LC, with controls."""
from pathlib import Path
from math import comb
from random import Random
from collections import Counter
import hashlib,json,time
from audit_joint_structure import fastconv
from audit_arbitrary_Fibonacci_tail_late_C import sub,mul,sign
from audit_binary_CI_infinite_padding_entrance import binary


def arrays(V,m,alpha):
    L=[1]
    for t in V:L=fastconv(L,[1]*t)
    C=fastconv(L,binary(m));E=fastconv(L,[comb(m+1,j) for j in range(m+2)])
    off=m+alpha;N=max(len(C),off+len(E))
    raw=[(C[n] if n<len(C) else 0)-(E[n-off] if 0<=n-off<len(E) else 0)
         for n in range(N)]
    A=[max(0,x) for x in raw]
    b=[sub((0,A[n-1] if n else 0),(A[n],0)) for n in range(N)]
    return L,C,E,raw,A,b


def main():
    start=time.monotonic();rng=Random(20261029724);ct=Counter();sha=hashlib.sha256();bad=None;post_controls=[]
    controls=[]
    for V,m,alpha,n,kind,expected in [
        ((3,10,17,19),45,3,77,'source_ratio_convexity',-271323914621406621683974923994713145233811263),
        ((20,21),41,3,69,'actual_infinite_relative_LC',-1175523533570113741138335149183802344680486518056376)]:
        L,C,E,raw,A,b=arrays(V,m,alpha)
        if kind=='source_ratio_convexity':
            get=lambda j:E[j-m-alpha] if 0<=j-m-alpha<len(E) else 0
            margin=get(n-1)*C[n]*C[n+1]-2*get(n)*C[n-1]*C[n+1]+get(n+1)*C[n-1]*C[n]
        else:margin=A[n]**2*C[n-1]*C[n+1]-A[n-1]*A[n+1]*C[n]**2
        assert margin==expected and margin<0 and A[n]>0
        controls.append(dict(V=V,m=m,alpha=alpha,n=n,kind=kind,margin=margin,first_mode=A.index(max(A))))
    L,C,E,raw,A,b=arrays((13,),15,12)
    M=sub(mul(b[29],b[29]),mul(b[28],b[30]))
    assert A.index(max(A))==26 and M==(144665649,-92463597) and sign(M)<0
    controls.append(dict(V=[13],m=15,alpha=12,n=29,kind='CLIPPED_deficit_LC_after_first_A_mode',
        margin=M,first_mode=26,A_triple=A[28:31],A_minor=A[29]**2-A[28]*A[30]))
    for trial in range(6000):
        V=sorted(rng.choices(range(3,26),k=rng.randint(1,9)));h=sum(t-1 for t in V)
        m=h if trial%3 else h+rng.randint(0,10);alpha=rng.randint(1,h)
        L,C,E,raw,A,b=arrays(V,m,alpha);ell=A.index(max(A));off=m+alpha
        prevE=0
        for n in range(1,len(C)):
            curE=E[n-off] if 0<=n-off<len(E) else 0
            assert curE*C[n-1]>=prevE*C[n]
            prevE=curE;ct['exact_all_rank_LR_source_comparisons']+=1
        for n in range(m+1,len(A)-1):
            if A[n]<=0:break
            assert sign(b[n])>0
            ct['exact_positive_clipped_geometric_deficits']+=1
            if n>=m+2:
                M=sub(mul(b[n],b[n]),mul(b[n-1],b[n+1]))
                ct['finite_only_clipped_geometric_deficit_LC_minors']+=1
                if n<=ell:ct['finite_only_through_first_mode_deficit_LC_minors']+=1
                if sign(M)<0:
                    if n<=ell:
                        bad=dict(V=V,m=m,alpha=alpha,n=n,first_mode=ell,
                            A_triple=A[n-1:n+2],b_triple=b[n-1:n+2],minor=M);break
                    ct['post_first_mode_clipped_deficit_LC_failures']+=1
                    if len(post_controls)<3:
                        post_controls.append(dict(V=V,m=m,alpha=alpha,n=n,first_mode=ell,minor=M))
        ct['actual_short_padding_contexts']+=1
        if m==h:ct['actual_single_entrance_contexts']+=1
        sha.update(json.dumps([V,m,alpha,A,b],separators=(',',':')).encode())
        if bad:break
    out=dict(status='FINITE_ONLY_OPEN_SHORT_PADDING_CLIPPED_DEFICIT_LC_DIAGNOSTIC',counts=dict(ct),
        counter=bad,negative_controls=controls,additional_post_mode_controls=post_controls,
        state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='Universal FULL positive-tail clipped-deficit LC is FALSE, including a one-jump example. THROUGH FIRST A MODE remains OPEN and all such entries are finite diagnostics only. No universal actual short-padding entrance, general C/A2 or original UI conclusion. LR positivity has a separate written proof.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
