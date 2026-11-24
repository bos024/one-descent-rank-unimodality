"""Exact QA only of the all-parameter complete-C two-jump theorem."""
from pathlib import Path
import sys,json,time,hashlib
from itertools import accumulate
from random import Random
from collections import Counter
from fractions import Fraction as Q
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import rebuild,c_minimum
from audit_arbitrary_Fibonacci_tail_late_C import sign

def geq2(v):
    v=Q(v);return sign((v.numerator-2*v.denominator,v.denominator))>=0

def main():
    rng=Random(20261031517);ct=Counter();sha=hashlib.sha256();start=time.monotonic();witnesses=[]
    profiles=[]
    for u in range(0,61):
        for L in {3,4,max(3,u+1),max(3,u+2),max(3,u+3),2*u+7}:
            for t in {L,L+3,2*L+1}:profiles.append((u,L,t))
    for _ in range(450):
        u=rng.randint(0,110);L=rng.randint(3,140);t=rng.randint(L,L+170);profiles.append((u,L,t))
    for u,L,t in profiles:
        for alpha in {1,2,2*u+L+t}:
            old=arm_prefix(alpha,[2]*u+[L],alpha+2*u+L+1)
            od=[0,0]+[max(0,old[n]-old[n-1]) for n in range(2,len(old))];ell=od.index(max(od))
            kappa=next(n for n in range(2,len(old)) if old[n]<2**(n-1))
            assert kappa==(4 if u else 3);K=4
            assert 2*ell<=3*u+L+2
            F=arm_prefix(alpha,[2]*u+[L,t],alpha+2*u+L+t+1)
            D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
            c_minimum(F,D,4,len(F)-1,ct);ct['all_parameter_actual_twojump_hosts']+=1
            G=list(accumulate(old))
            if u>=5 and u<L-1:
                for j in range(2,len(old)-1):
                    assert old[j]**2>=old[j-1]*old[j+1];ct['deficit_onejump_GLOBAL_ordinary_LC_from2']+=1
            for n in range(t+5,min(ell,L+t-1)+1):
                assert u>=5 and L>=5
                if D[n]<=D[n-1] or not D[n-1]:continue
                mu=Q(D[n],D[n-1]);s=n-t
                assert sign((-mu.numerator,mu.denominator))>0
                if u>=L-1 and n<=u+3:
                    ct['twojump_protected_reference_complete_C_payments']+=1;continue
                assert mu*old[n-2]<=old[n-1]
                if u>=L-1:
                    assert sign((old[s-1],-old[s-2]))>0
                    ct['surplus_strict_actual_window_payments']+=1
                else:ct['deficit_strict_actual_window_payments']+=1
                for k in range(1,n-1):
                    assert geq2(G[k]-mu*G[k-1]);ct['ALL_old_G_prefix_margin_payments']+=1
            sha.update(json.dumps([alpha,u,L,t,ell,kappa,D[L+t-1:L+t+1]],separators=(',',':')).encode())
            if u==20 and L==12 and t==15 and alpha==1:witnesses.append(dict(alpha=alpha,u=u,L=L,t=t))
        R=rebuild([L,t],L+t+9);d=[0,0]+[max(0,R[n]-R[n-1]) for n in range(2,len(R))]
        c_minimum(R,d,4,len(R)-1,ct);ct['same_tail_reference_entire_C_profiles']+=1
        for n in range(t+3,t+L+2):
            assert sign((-d[n],d[n-1]))>0;ct['reference_TWO_jump_golden_window_gap_reads']+=1
    out=dict(status='EXACT_QA_UNBOUNDED_TWO_NONBINARY_COMPLETE_C_UNDER_AUDIT',counts=dict(ct),
      state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
      scope='WrittenunboundedcompleteCproofbyactualrankcover+conditionalwindow+center+univtail;finiteprofilesQAONLY,no finite premise. FullCwith>=3nonbinary/fullA2/originalUIOPEN.')
    (ROOT/'audit_two_nonbinary_complete_C.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
