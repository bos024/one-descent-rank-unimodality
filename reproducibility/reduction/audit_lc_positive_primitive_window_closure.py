"""Exact finite QA of the nonsymmetric window and unperturbed quotient closure."""
from pathlib import Path
from random import Random
from collections import Counter
from math import comb
import hashlib,json,time
from audit_joint_structure import fastconv
from audit_binary_CI_infinite_padding_entrance import quotient,convolution,minor
from audit_arbitrary_Fibonacci_tail_late_C import sub,sign


def main():
    started=time.monotonic();rng=Random(20261029742);ct=Counter();sha=hashlib.sha256()
    for trial in range(3500):
        h=rng.randint(1,35);den=rng.choice([4,8,12])
        ratios=sorted([rng.randint(1,4*den) for _ in range(h)],reverse=True)
        d=[den**h]
        for v in ratios:d.append(d[-1]*v//den)
        tail_length=rng.randint(1,28);scale=den**tail_length
        a=[];value=0
        for v in d:value+=v*scale;a.append(value)
        for v in sorted([rng.randint(1,den-1) for _ in range(tail_length)],reverse=True):
            assert a[-1]*v%den==0
            a.append(a[-1]*v//den)
        assert all(a[n]**2>=a[n-1]*a[n+1] for n in range(1,len(a)-1))
        for t in [2,rng.randint(2,len(a)+6)]:
            C=fastconv(a,[1]*t)
            # DIFFERENCE THE EXACT INTEGERS. A floating subtraction of
            # two large windows gives false failures near tiny tails.
            delta=[]
            for n,v in enumerate(C):
                w=v-(C[n-1] if n else 0)
                if w<=0:break
                delta.append(w)
            for n in range(1,len(delta)-1):
                assert delta[n]**2>=delta[n-1]*delta[n+1],('window',a,t,n)
                ct['exact_nonsymmetric_uniform_window_primitive_minors']+=1
            ct['nonsymmetric_window_contexts']+=1
            sha.update(json.dumps([a,t,delta],separators=(',',':')).encode())
        w=[rng.randint(1,9),rng.randint(1,9)];C=fastconv(a,w);delta=[]
        for n,v in enumerate(C):
            dd=v-(C[n-1] if n else 0)
            if dd<=0:break
            delta.append(dd)
        for n in range(1,len(delta)-1):
            assert delta[n]**2>=delta[n-1]*delta[n+1]
            ct['exact_weighted_binary_primitive_minors']+=1
        ct['weighted_binary_contexts']+=1
    for trial in range(2200):
        V=rng.choices(range(1,20),k=rng.randint(0,8));u=rng.randint(0,70);L=[1]
        for t in V:L=fastconv(L,[1]*t)
        for extra in [[1],[2,1],[1,2,1]]:
            LL=fastconv(L,extra);B=convolution(quotient(u),LL)
            for n in range(1,len(B)-1):
                assert sign(minor(B,n))>=0
                ct['exact_ordinary_LC_quotient_product_minors']+=1
            delta=[]
            for n,v in enumerate(B):
                w=sub(v,B[n-1] if n else (0,0))
                if sign(w)<=0:break
                delta.append(w)
            for n in range(1,len(delta)-1):
                assert sign(minor(delta,n))>=0,('quotient primitive',u,V,extra,n)
                ct['exact_quotient_product_positive_primitive_minors']+=1
            ct['CI_quotient_product_contexts']+=1
            sha.update(json.dumps([u,V,extra,B,delta],separators=(',',':')).encode())
    for trial in range(1600):
        den=rng.randint(2,30);num=rng.randint(1,den-1);u=rng.randint(0,60)
        scale=den**u;P=[]
        for n in range(u+1):
            assert not n or P[-1]*num%den==0
            P.append(comb(u,n)*scale-(P[-1]*num//den if n else 0))
        L=[1]
        for t in rng.choices(range(1,20),k=rng.randint(0,7)):
            L=fastconv(L,[1]*t)
        B=fastconv(P,L)
        assert all(B[n]**2>=B[n-1]*B[n+1] for n in range(1,len(B)-1))
        delta=[]
        for n,v in enumerate(B):
            dd=v-(B[n-1] if n else 0)
            if dd<=0:break
            delta.append(dd)
        for n in range(1,len(delta)-1):
            assert delta[n]**2>=delta[n-1]*delta[n+1]
            ct['exact_non_golden_rational_quotient_primitive_minors']+=1
        ct['arbitrary_rational_q_CI_quotient_contexts']+=1
        sha.update(json.dumps([num,den,u,L,B,delta],separators=(',',':')).encode())
    out=dict(status='PASS_EXACT_QA_WRITTEN_NONSYMMETRIC_WINDOW_AND_UNPERTURBED_QUOTIENT_PRIMITIVE_LC',
        counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-started,
        scope='Finite exact QA of the written unbounded generic window theorem and unperturbed Q_u CI products. No actual spectral perturbation removed, no actual alpha1/2 entrance, no general C/A2/original UI conclusion.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
