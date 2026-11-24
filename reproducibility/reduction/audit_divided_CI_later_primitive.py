"""Exact independent QA of the proposed repaired ALL-degree primitive theorem."""
from pathlib import Path
from random import Random
from collections import Counter
import hashlib,json,time
from audit_joint_structure import fastconv
from audit_arbitrary_Fibonacci_tail_late_C import add,sub,mul,power,sign,evaluate,absolute
from audit_binary_CI_infinite_padding_entrance import quotient,convolution,minor
from probe_divided_CI_positive_primitive import divided
from audit_padding_three_local_prefix import parts,primitive,positive
Q=(-1,1);PHI=(0,1);PSI=(1,-1);ZERO=(0,0);ONE=(1,0)
def scale(k,x):return mul((k,0),x)

def main():
    start=time.monotonic();rng=Random(20261029758);ct=Counter();sha=hashlib.sha256();small=[];cert=set()
    for u in range(1,12):
        for p in parts(u-1):
            L=[1]
            for x in p:L=fastconv(L,[1]*(x+1))
            _,J=divided(L,u);dp=positive(primitive(J))
            for n in range(2,len(dp)-1):
                M=minor(dp,n);assert sign(M)>=0,(u,p,n,M);cert.add(M)
                ct['complete_small_later_primitive_minors']+=1
            small.append(dict(u=u,degree_partition=p,J=J,positive_primitive=dp))
    assert len(small)==139
    cert=sorted(cert)
    den=10**16;lo=16180339887498948;hi=lo+1
    assert all(den*a+b*(lo if b>=0 else hi)>=0 for a,b in cert)
    for u in range(12,81):
        QQ=quotient(u)
        for s in range(2,u-1):
            row0=sub(QQ[s],mul(power(Q,s),add((3*u-3,0),scale(2,Q))))
            assert sign(row0)>=0
            ct['exact_double_robust_row_zero_payments']+=1
            for k in range(1,s+1):
                T=add(add(QQ[k+1],scale(2,mul(Q,QQ[k]))),mul(power(Q,2),QQ[k-1]))
                K=sub(mul(QQ[s],QQ[k]),mul(QQ[s+1],QQ[k-1]))
                assert sign(sub(K,scale(2,mul(power(Q,s),T))))>=0
                ct['exact_double_robust_kernel_rows']+=1
        for t in [u-1,u]:
            _,J=divided([1]*t,u);d=primitive(J)
            if t==u:assert d[u]==sub(power(PSI,u),ONE) and sign(d[u])<0
            else:
                assert d[u-1]==add(Q,power(PSI,u)) and sign(d[u-1])>0
                assert d[u]==sub(add((-u,0),Q),mul(Q,power(PSI,u))) and sign(d[u])<0
            ct['exact_two_exceptional_single_interval_boundary_formulas']+=1
    for trial in range(500):
        u=rng.randint(12,55);a=rng.randint(1,(u-3)//2);N=[1];ratio=a
        for n in range(rng.randint(1,2*u)):
            if n and rng.random()<.25:ratio=max(1,ratio-1)
            N.append(N[-1]*ratio)
        B=convolution(quotient(u),N)
        for s in range(2,u-1):
            T=add(add(B[s+1],scale(2,mul(Q,B[s]))),mul(power(Q,2),B[s-1]))
            assert sign(sub(minor(B,s),scale(2,mul(power(Q,s),T))))>=0
            ct['exact_generic_double_robust_head_minors']+=1
        ct['generic_LC_double_budget_contexts']+=1
    for trial in range(1600):
        Vold=rng.choices(range(3,26),k=rng.randint(0,8));t=rng.randint(3,30);V=Vold+[t]
        h=sum(x-1 for x in V);u=max(12,h+1+rng.randint(0,5));r=len(Vold)
        L0=[1]
        for x in Vold:L0=fastconv(L0,[1]*x)
        L=fastconv(L0,[1]*t);E,J=divided(L,u);d=primitive(J);dp=positive(d)
        B=convolution(quotient(u),L0);c=evaluate(E,(0,-1));aa=mul(mul(PHI,PHI),c)
        assert sign(sub(scale(2,Q),absolute(aa)))>=0
        if r:assert sign(sub(ONE,absolute(aa)))>=0
        X=[sub(B[n],mul(aa,power(PSI,n))) for n in range(u)]
        assert all(sign(x)>0 for x in X[1:])
        for s in range(2,u-1):
            assert sign(minor(X,s))>=0
            ct['exact_double_perturbed_X_head_minors']+=1
        for n in range(1,min(t,u)):assert d[n]==X[n]
        if t<u:assert d[t]==sub(X[t],ONE)
        if t+1<u:assert d[t+1]==sub(X[t+1],B[1])
        ct['exact_repaired_low_head_identity_contexts']+=1
        if t<=u-2:
            gap=sub(mul(B[1],B[t-1]),scale(2,B[t]));gapx=sub(mul(B[1],X[t-1]),scale(2,X[t]))
            if r:
                assert sign(sub(gap,(u,0)))>=0
                assert sign(sub(scale(5,gapx),(2*u,0)))>=0
                ct['exact_nonempty_old_tail_strong_junction_payments']+=1
            else:
                assert sign(sub(gap,sub((u,0),mul(Q,Q))))>=0
                assert sign(sub(scale(30,gapx),(15*u-22,0)))>=0
                ct['exact_empty_old_tail_strong_junction_payments']+=1
            assert minor(d,t)==add(add(minor(X,t),gapx),ONE)
        # The WEAK window conclusion starts only at t+1, never centre t.
        _,Jo=divided(L0,u);win=convolution(Jo,[1]*t);dwin=positive(primitive(win))
        for n in range(t+1,len(dwin)-1):
            assert sign(minor(dwin,n))>=0
            ct['exact_later_only_primitive_window_minors']+=1
        for n in range(2,len(dp)-1):
            assert sign(minor(dp,n))>=0,('entire later primitive',V,u,n)
            ct['exact_entire_CI_later_primitive_minors']+=1
        ct['repaired_CI_induction_contexts']+=1
        sha.update(json.dumps([V,u,J,d,X],separators=(',',':')).encode())
    _,J=divided([1,1,1],3);first=minor(positive(primitive(J)),1)
    assert first==(11,-7) and sign(first)<0
    out=dict(status='PASS_EXACT_QA_REPAIRED_ALL_DEGREE_LATER_DIVIDED_CI_PRIMITIVE',counts=dict(ct),
        small_contexts=small,small_scalar_certificate=cert,small_scalar_certificate_count=len(cert),
        rational_root_interval=dict(denominator=den,lower=lo,upper=hi),
        unavoidable_first_primitive_counter=dict(V=[3],u=3,n=1,minor=list(first)),
        state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='Exact QA ONLY of a new WRITTEN unbounded double-budget/later-window interval induction and complete139 bounded exceptions. The repaired theorem is NOT registered until its formal audits pass. First primitive centre intentionally excluded; no original C/A2/UI claim.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['small_contexts','small_scalar_certificate']}),flush=True)

if __name__=='__main__':main()
