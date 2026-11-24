"""Exact QA for the fixed terminal fourteen UNBOUNDED proof, not a finite premise."""
from pathlib import Path
from fractions import Fraction as Q
from random import Random
from math import prod
from collections import Counter
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_binary_first_defect_ordinary_tail import arm
from audit_joint_structure import fastconv
rho=Q(3,5);b=Q(35,32);c=Q(3,2);q=Q(6125,6144);offset=Q(125,22)
def at(A,n):return A[n] if 0<=n<len(A) else 0
def relative(t):return c*(1-rho**t)/b**(t-1)
def missing(U):return min([len(U)+2]+[t+len(U)-i for i,t in enumerate(U)])
def scalar(alpha,U):
    f=Q(5,2)*(1-rho**(alpha+1))
    for t in U:f=1+c*(1-rho**t)*f
    return f
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=Random(2026110216)
    Pstar=relative(4)**2*prod(relative(t) for t in range(5,13))
    assert Q(41472,125)*Pstar<=b**39
    assert q**16<=Q(20,21)
    for a in range(200):assert (a+1)*Q(20,21)**a<=8
    for t in range(3,501):
        if t>=4:assert relative(t+1)<=relative(t)
        for L in [3,4,5,10,min(t,30)]:
            if L<=t:assert relative(t)<=relative(max(4,L))
        ct['whole_relative_capacity_scalar_QA']+=1
    for m in range(1001):
        assert m*q**m<=128 and (m+1)*rho**m<=Q(6,5)
        if m>=80:assert 10*(m+1)*Q(175,192)**m<=1
        ct['whole_block_kernel_large_read_power_QA']+=1
    profiles=[]
    for K in [16,17,18,20,25]:
        profiles += [(1,list(range(2,K))),(1,[K-1]*(K-2)),(50*K,list(range(2,K))),
            (1,list(range(2,K-1))+[50*K])]
        for t in [2,3,4,5]:
            for g in [t-1,10,40,100]:profiles.append((1,[t]*max(g,t-1)+list(range(t+1,K))))
    for _ in range(60):
        K=rng.randrange(16,25);g=K-2+rng.randrange(5);beta=rng.randrange(1,12)
        V=[max(2,K-g+i) for i in range(g)];extra=0
        for i in range(g):
            if rng.randrange(4)==0:extra+=rng.randrange(5)
            V[i]+=extra
        assert missing(V)>=K;profiles.append((beta,V))
    for beta,V in profiles:
        K=missing(V);assert K>=16 and len(V)>=14
        assert all(V[-14+i]>=i+2 for i in range(14))
        middle=V[-13:-3];assert len(middle)==10 and all(t>=i+3 for i,t in enumerate(middle))
        p=prod(relative(t) for t in middle);assert p<=Pstar
        G=arm(beta,V[:-3])[:-2];F=arm(beta,V)[:-2];pre=arm(beta,V[:-1])[:-2]
        v0,u,T=V[-3:];M=beta+sum(t-1 for t in V);MG=beta+sum(t-1 for t in V[:-3]);A=beta+sum(t-1 for t in V[:-2])
        assert A>=79 and M-MG>=39
        if len(G)<900:
            gp=scalar(beta,V[:-3]);assert gp+offset<=10*b**MG*p
            ct['WHOLE_actual_middle_tail_offset_norm_QA']+=1
        H=fastconv(fastconv([1]*u,[1]*v0),G)
        B=max([beta]+[t-1 for t in V]);S=min(M//2,M-B)
        for m in range(S+1,len(F)+2):
            d=at(F,m)-at(F,m-1)
            assert m*d<=1<<m
            ct['ALL_actual_signed_slopes_OUTSIDE_strict_head']+=1
            if M<=2*m:
                assert m-1>u and m>=3
                assert at(pre,m-1)==at(H,m-3)
                assert d<=at(H,m-3)
                ct['ALL_bulk_ACTUAL_source_unit_vanish_and_two_interval_read_QA']+=1
            else:ct['ALL_NONBULK_actual_signed_slope_QA']+=1
        ct['actual_first_missing_sixteen_plus_profiles']+=1
        sha.update(repr((beta,V,F,S,p)).encode())
    # A genuine lower-threshold failure, not an original-unimodality counterexample.
    U=[4]*30+list(range(5,11));F=arm(1,U);M=1+sum(t-1 for t in U);S=M//2;m=66;d=F[m]-F[m-1]
    assert missing(U)==11 and S==65 and d==1150738045674555652 and m*d>1<<m
    out=dict(status='PASS_QA_UNBOUNDED_FIXED_TERMINAL_FOURTEEN_SLOPE_THINNESS',counts=dict(ct),
      exact_template_margin=dict(numerator=(b**39-Q(41472,125)*Pstar).numerator,denominator=(b**39-Q(41472,125)*Pstar).denominator),
      genuine_kappa_eleven_thinness_counter=dict(alpha=1,U=U,m=m,strict_head=S,slope=d),
      state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      scope='QA ONLY. Exact scalar constants and whole fixed fourteen model/read checks. No finite word proof premise, no claim belowkappa16, no generalC/A2/original conclusion.')
    (ROOT/'audit_fixed_terminal_fourteen_slope.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='exact_template_margin'}),flush=True)
if __name__=='__main__':main()
