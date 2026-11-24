"""Exact finite diagnostics of OPEN divided-CI positive-primitive assertions."""
from pathlib import Path
from math import comb
from random import Random
from collections import Counter
import hashlib,json,time
from audit_joint_structure import fastconv
from audit_arbitrary_Fibonacci_tail_late_C import sub,mul,sign,evaluate
from audit_binary_CI_infinite_padding_entrance import minor
Q=(-1,1);ZERO=(0,0)


def divided(L,U):
    E=fastconv(L,[comb(U,j) for j in range(U+1)])
    c=evaluate(E,(0,-1));J=[]
    for n,v in enumerate(E):
        J.append(sub((v,0),c) if n==0 else sub((v,0),mul(Q,J[-1])))
    assert J[-1]==ZERO
    return E,J[:-1]


def primitive(J):
    d=[]
    for n,v in enumerate(J):
        w=sub(v,J[n-1] if n else ZERO)
        if sign(w)<=0:break
        d.append(w)
    return d


def main():
    started=time.monotonic();rng=Random(20261029744);ct=Counter();sha=hashlib.sha256();bad=None
    E,J=divided([1,1,1],3);d=primitive(J)
    assert minor(d,1)==(11,-7) and sign(minor(d,1))<0
    for trial in range(6000):
        V=rng.choices(range(3,29),k=rng.randint(1,9));h=sum(t-1 for t in V);L=[1]
        for t in V:L=fastconv(L,[1]*t)
        for surplus in [1,rng.randint(2,8)]:
            U=h+surplus;E,J=divided(L,U);d=primitive(J)
            for n in range(1 if surplus>=2 else 2,len(d)-1):
                M=minor(d,n)
                ct['finite_only_later_primitive_minors' if surplus==1 else 'finite_only_full_primitive_minors']+=1
                if sign(M)<0:
                    bad=dict(V=V,U=U,h=h,surplus=surplus,n=n,margin=M,triple=d[n-1:n+2])
                    break
            ct['CI_divided_primitive_contexts']+=1
            sha.update(json.dumps([V,U,J,d],separators=(',',':')).encode())
            if bad:break
        if bad:break
    out=dict(status='FINITE_ONLY_OPEN_DIVIDED_CI_POSITIVE_PRIMITIVE_DIAGNOSTIC',
        counts=dict(ct),counter=bad,negative_control=dict(V=[3],U=3,n=1,minor=[11,-7]),
        state_sha256=sha.hexdigest(),seconds=time.monotonic()-started,
        scope='The TWO repaired primitive assertions remain OPEN. Full primitive LC at U=h+1 is FALSE already at its first internal centre. Exact alpha2 algebraic reduction is written separately; no actual alpha2 entrance, general C/A2 or original UI conclusion.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
