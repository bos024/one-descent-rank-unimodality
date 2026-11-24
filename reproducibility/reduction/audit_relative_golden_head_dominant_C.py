"""Exact field and actual-word QA of relative golden heads/dominant full C."""
from pathlib import Path
import sys,json,time,hashlib
from itertools import accumulate
from fractions import Fraction as Frac
from collections import Counter
from random import Random
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_arbitrary_Fibonacci_tail_late_C import sign,add,sub,mul,power
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import rebuild,c_minimum
Q=(-1,1);PSI=(1,-1);ONE=(1,0);C=power(Q,6)

def geq2(x):
    x=Frac(x);return sign((x.numerator-2*x.denominator,x.denominator))>=0

def main():
    rng=Random(20261031541);ct=Counter();sha=hashlib.sha256();start=time.monotonic()
    profiles=[[3],[3,4],[4,3],[3]*20,[4]*18,[3,4]*10]
    profiles += [rng.choices(range(3,22),k=rng.randint(1,14)) for _ in range(200)]
    for V in profiles:
        a=sum(V);R=rebuild(V,a+12);rho=(R[a],-R[a-1]);prod=ONE
        for t in V:prod=mul(prod,mul(Q,sub(ONE,power(PSI,t))))
        assert rho==prod and sign(rho)>0 and sign(sub(ONE,rho))>0
        for n in range(2,a+1):
            assert sign(sub((R[n],-R[n-1]),mul(C,rho)))>=0
            ct['arbitrary_ORDER_reference_entire_relative_head_q6_reads']+=1
        for n in range(a,a+12):
            assert (R[n],-R[n-1])==mul(power(PSI,n-a),rho)
            ct['exact_terminal_spectral_tail_normalization_reads']+=1
    for _ in range(35):
        V=sorted(rng.choices(range(3,12),k=2))
        for depth in range(2):
            a=sum(V);r=len(V);h=a-r;t=2*a+rng.randint(0,4);W=a+t
            RR=rebuild(V+[t],W+8);rd=[0,0]+[RR[n]-RR[n-1] for n in range(2,len(RR))]
            c_minimum(RR,rd,4,len(RR)-1,ct);ct['dominant_extended_FULL_reference_C_profiles']+=1
            for u in {0,4,max(0,h-1),h,(3*a)//2,2*a}:
                for alpha in {1,u+h+3}:
                    old=arm_prefix(alpha,[2]*u+V,alpha+2*u+a+1);G=list(accumulate(old))
                    od=[0,0]+[max(0,old[n]-old[n-1]) for n in range(2,len(old))];ell=od.index(max(od))
                    F=arm_prefix(alpha,[2]*u+V+[t],alpha+2*u+W+1)
                    D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
                    c_minimum(F,D,4,len(F)-1,ct);ct['all_binary_dominant_FULL_actual_C_hosts']+=1
                    assert 2*ell<=3*u+a+r+1
                    if u<h or u+r<=5:
                        assert ell<=t+4;ct['deficit_OR_small_count_ALL_mode_payments']+=1
                    else:
                        L=u+r+1
                        for n in range(max(t+5,L+2),min(ell,W-1)+1):
                            A,B=D[n-1:n+1]
                            if B<=A or not A:continue
                            mu=Frac(B,A);s=n-t
                            assert 2<=s-1<=L and n-1>=max(a,L+1)
                            assert sign((old[s-1],-old[s-2]))>0 and sign((-old[n-1],old[n-2]))>0
                            assert B*old[n-2]<A*old[n-1]
                            for k in range(1,n-1):
                                assert geq2(G[k]-mu*G[k-1]);ct['dominant_surplus_FULL_old_G_q2_payments']+=1
                            ct['dominant_surplus_strict_actual_window_payments']+=1
                    sha.update(json.dumps([alpha,u,V,t,ell,D[W-1:W+1]],separators=(',',':')).encode())
            V=V+[t]
    out=dict(status='EXACT_QA_UNIVERSAL_RELATIVE_GOLDEN_HEAD_AND_DOMINANT_C_UNDER_AUDIT',counts=dict(ct),
      state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
      scope='UniversalALL-orderHprefix>=q6rho anduniformFULLCdominantappendt>=2oldNONBINARYweight. Arbitrarynumberofappendsbywritteninduction,no finite premise. GeneralnondominantC/A2/originalUIOPEN.')
    (ROOT/'audit_relative_golden_head_dominant_C.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
