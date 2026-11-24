"""Exact QA only for the all-count proper-quotient norm cone."""
from pathlib import Path
from collections import Counter
from fractions import Fraction as Q
import sys,json,time,hashlib,random
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_tribonacci_quadratic_inverse import ZERO,ONE,A,B,add,sub,mul,power,sign,pc
from build_tribonacci_rich_reverse_certificate import reverse
def scale(v,c):return tuple(x*c for x in v)
def Epoly(r,s):
    E=[1]
    for t in [3]*r+[4]*s:E=pc(E,[1]*t)
    return E
def remainder(E,J):return sub((E[0],0,0),J[0]),sub(sub((E[1],0,0),J[1]),mul(A,J[0]))
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=random.Random(110103)
    contexts={(r,s) for r in range(32,113,4) for s in range(0,40,3)}
    contexts|={(3*s-4+d,s) for s in range(16,81,2) for d in [0,5,20]}
    for r,s in sorted(contexts):
        norm=scale(power(B,r+1),4**s)
        if sign(sub(ONE,scale(norm,64)))<0:continue
        E=Epoly(r,s);J=reverse(E);R0,R1=remainder(E,J)
        observed=add(sub(mul(B,mul(R0,R0)),mul(A,mul(R0,R1))),mul(R1,R1))
        assert observed==norm
        for v in [R0,R1]:assert sign(sub(ONE,scale(v,4)))>=0 and sign(add(ONE,scale(v,4)))>=0
        for v in J:assert sign(v)>0;ct['whole_proper_quotient_positive_coefficients']+=1
        for n in range(1,len(J)-1):
            assert sign(sub(mul(J[n],J[n]),mul(J[n-1],J[n+1])))>=0
            ct['whole_proper_quotient_GLOBAL_LC_minors']+=1
        Jnew=reverse(pc(E,[1]*4));nextR=remainder(pc(E,[1]*4),Jnew)
        out=[ZERO]*(len(J)+3)
        for i,v in enumerate(J):
            for j in range(4):out[i+j]=add(out[i+j],v)
        out[0]=sub(out[0],R0)
        out[1]=add(sub(out[1],R1),mul((0,1,0),R0))
        out[2]=add(out[2],mul((0,1,0),R1))
        assert out==Jnew and nextR==(scale(R0,2),scale(R1,2))
        ct['EXACTproper_forward_low_THREE_rank_correction_contexts']+=1
        ct['norm_cone_hosts']+=1
        if s>=16 and r>=3*s-4:ct['explicit_unbounded_cone_QA_hosts']+=1
        sha.update(str((r,s,R0,R1,J[:5],J[-3:])).encode())
    # Test the complete real-box head independently of the special cubic root.
    for _ in range(2500):
        w=Q(32)+Q(rng.randrange(20000),23);r=Q(rng.randrange(1001),1000)*w;s=w-r
        a=Q(rng.randrange(1001),1000);b=Q(rng.randrange(1001),1000)
        R0=Q(rng.randrange(-1000,1001),4000);R1=Q(rng.randrange(-1000,1001),4000)
        E2=w*(w+1)/2;E3=w*(w+1)*(w+2)/6-r;E4=w*(w+1)*(w+2)*(w+3)/24-r*w-s
        J=[1-R0];J.append(w-a*J[0]-R1)
        for en in [E2,E3,E4]:J.append(en-a*J[-1]-b*J[-2])
        assert min(J[:3])>0 and all(J[n]**2>=J[n-1]*J[n+1] for n in [1,2,3])
        ct['EXACTrational_FULLreal_box_THREE_head_minor_contexts']+=1
    out=dict(status='EXACT_QA_PASS_MIXED_THREE_FOUR_PROPER_QUOTIENT_NORM_CONE',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      scope='ALLr>=32,s>=0withb^(r1)4^s<=1/64:positiveGLOBALordinaryLCproperJ;explicitALLs>=16/r>=3s-4. Pure3baseREUSED;NOnewfiniteproofpremise. HeadordinaryLCNOTprimitiveLC/actualD;actual/generalC/A2/originalUIremainOPEN.')
    (ROOT/'audit_mixed_three_four_proper_quotient.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
