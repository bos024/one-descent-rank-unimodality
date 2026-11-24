"""Exact finite QA of the arbitrary-order ordinary golden prefix and universal tilted seed."""
from pathlib import Path
import sys,json,time,hashlib
from itertools import product,accumulate
from fractions import Fraction as Q
from random import Random
from collections import Counter
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_homogeneous_reference_and_sharp_entrance import rebuild
from audit_arbitrary_Fibonacci_tail_late_C import sign,add,mul,sub,power
from audit_minimum_staircase_scaled_dyadic import arm_prefix
def main():
    rng=Random(20261031383);ct=Counter();sha=hashlib.sha256();start=time.monotonic()
    profiles=list(product(range(3,9),repeat=3))
    profiles+=[tuple(rng.choices(range(3,42),k=rng.randint(1,12))) for _ in range(1600)]
    for V in profiles:
        W=sum(V);R=rebuild(V,W+1)
        for n in range(2,W+1):
            assert sign((R[n],-R[n-1]))>0;ct['arbitrary_order_full_ordinary_golden_prefix_reads']+=1
        if len(V)>1:
            old=V[:-1];t=V[-1];O=rebuild(old,W+4);H=[(O[0],0)]+[(O[n],-O[n-1]) for n in range(1,len(O))]
            for n in range(2,W+2):
                cur=(0,0)
                for j in range(max(0,n-t),n):cur=add(cur,H[j])
                assert cur==(R[n],-R[n-1]);ct['exact_full_append_gap_window_identities']+=1
        if W<=95:
            d=[0,0]+[R[n]-R[n-1] for n in range(2,len(R))];lam=Q(d[W+1],d[W])
            for a in {Q(1),Q(3,4),Q(9,10)}:
                mu=a*lam
                if mu<=1:continue
                T=[Q(1),Q(1)]
                for n in range(2,W+1):T.append(T[-1]+a**(n-2)*d[n])
                assert T[W]-mu*T[W-1]>0
                H=[Q(1)]+[R[n]-lam*R[n-1] for n in range(1,W+1)]
                assert min(H[2:])>0
                rhs=a**W*H[W]+(1-a)*sum(a**i*H[i] for i in range(W))+(a*a-1)*(1-mu)
                assert rhs==a*a*(T[W]-mu*T[W-1]);ct['generic_reference_exact_ordinary_tilt_seed_identities']+=1
        sha.update(json.dumps([V,R[W-2:W+2]],separators=(',',':')).encode());ct['reference_profiles']+=1
    R=rebuild([3,4],7);assert (R[5],-R[4])==power((-1,1),6)
    ct['analytic_W3_exception_equality_q6']+=1
    out=dict(status='EXACT_QA_REFERENCE_ORDINARY_GOLDEN_PREFIX_AND_GENERAL_RECORD_CRITERION_UNDER_AUDIT',
      counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
      scope='Unbounded ordinaryreferenceprefix theorem and genericnormalizedtiltordinaryseed,allorders/counts/caps. ActualdensityrecordcriterionSUFFICIENTonly;universalrecordassertionOPEN. No finite entrance premise;finiteQAonly;original/generalC/A2OPEN.')
    (ROOT/'audit_reference_ordinary_golden_prefix.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()

