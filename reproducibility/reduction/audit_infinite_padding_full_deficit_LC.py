"""Independent exact finite QA of the written whole-tail deficit refinement."""
from pathlib import Path
from math import comb
from random import Random
from collections import Counter
import hashlib, json, time
from audit_joint_structure import fastconv
from audit_arbitrary_Fibonacci_tail_late_C import add, sub, mul, power, sign
from audit_binary_CI_infinite_padding_entrance import binary, quotient, convolution, minor

Q=(-1,1)
ZERO=(0,0)


def T(P,k):
    at=lambda n:P[n] if 0<=n<len(P) else ZERO
    return add(add(at(k+1),mul(mul((2,0),Q),at(k))),mul(mul(Q,Q),at(k-1)))


def main():
    started=time.monotonic();rng=Random(20261029733);ct=Counter();sha=hashlib.sha256()
    small={3:[(5,-3),(26,-15),(27,-16)],
        4:[(28,-17),(81,-48),(103,-61),(55,-33)],
        5:[(38,-23),(264,-160),(574,-349),(588,-359),(277,-170)]}
    for u in range(3,121):
        P=quotient(u);s=u-1
        for k in range(u):
            K=sub(mul(P[s],P[k]),mul(P[s+1],P[k-1]) if k else ZERO)
            margin=sub(K,mul(power(Q,s),T(P,k)))
            assert sign(margin)>0,('last kernel row',u,k,margin)
            if u in small:assert margin==small[u][k]
            ct['exact_final_quotient_kernel_row_budgets']+=1
        sha.update(json.dumps([u,P],separators=(',',':')).encode())
    for trial in range(1200):
        u=rng.randint(3,60);h=rng.randint(1,u-1)
        # Deliberately do NOT enforce L1 <= (u-1)/2: the LAST-centre
        # theorem needs only nonnegative LC and deg L <= u-1.
        ratios=sorted([rng.randint(1,80) for _ in range(h)],reverse=True);L=[1]
        for v in ratios:L.append(L[-1]*v)
        B=convolution(quotient(u),L);s=u-1
        assert sign(sub(minor(B,s),mul(power(Q,s),T(B,s))))>=0
        ct['exact_generic_LC_last_centre_budgets']+=1
        sha.update(json.dumps([u,L,B[s-1:s+2]],separators=(',',':')).encode())
    for trial in range(2500):
        V=rng.choices(range(3,28),k=rng.randint(1,9));h=sum(t-1 for t in V)
        m=h if trial%2 else h+rng.randint(1,15);L=[1]
        for t in V:L=fastconv(L,[1]*t)
        C=fastconv(L,binary(m))
        b=[ZERO]*(m+1)+[sub((0,C[n-1]),(C[n] if n<len(C) else 0,0))
            for n in range(m+1,len(C)+1)]+[ZERO]
        for n in range(m+1,len(C)+1):
            assert sign(b[n])>0
            ct['exact_entire_positive_deficit_support_reads']+=1
        for n in range(m+2,len(C)+1):
            assert sign(minor(b,n))>=0,('whole deficit LC',V,m,n)
            ct['exact_entire_deficit_LC_tail_minors']+=1
            if n==m+h+1:ct['exact_new_bridge_centre_minors']+=1
        ct['actual_CI_contexts']+=1
        if m==h:ct['actual_exact_single_entrance_contexts']+=1
        sha.update(json.dumps([V,m,b],separators=(',',':')).encode())
    out=dict(status='PASS_EXACT_QA_WRITTEN_WHOLE_INFINITE_PADDING_DEFICIT_LC',
        counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-started,
        scope='Finite exact QA of the separately written unbounded full infinite-padding deficit-tail LC theorem. Finite short padding/general C/A2/original UI remain OPEN. No finite exhaustion is a universal proof.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
