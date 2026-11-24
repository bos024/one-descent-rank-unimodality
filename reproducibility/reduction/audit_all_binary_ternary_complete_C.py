"""Exact actual all-count C and sharp ordinary-tail classification QA, not a finite proof."""
from pathlib import Path
from collections import Counter
from random import Random
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import c_minimum
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=Random(2026110165)
    cases=[(u,r,a) for r in range(0,21) for u in range(0,2*r+5) for a in [1,2,3,u+r+3]]
    cases +=[(rng.randint(0,200),rng.randint(0,150),rng.randint(1,300)) for _ in range(650)]
    for u,r,alpha in cases:
        F=arm_prefix(alpha,[2]*u+[3]*r,alpha+2*u+3*r+2);D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];L=D.index(max(D))
        c_minimum(F,D,4,L,ct);ct['ACTUAL_ALL_binary_ternary_count_hosts']+=1
        if r>=6 and u>=1:
            if u<=2*r:
                for n in range(r+3,len(F)-1):assert F[n]**2>=F[n-1]*F[n+1];ct['ACTUAL_ENTIRE_ordinary_LC_tail_minors_when_u_le_2r']+=1
                ct['sharp_classification_positive_hosts']+=1
            else:
                n=3*r+1;assert F[n]**2-F[n-1]*F[n+1]==-4**r
                ct['ACTUAL_EXACT_negative_four_power_classification_hosts']+=1
        sha.update(str((u,r,alpha,F,D,L)).encode())
    for u in list(range(10,81))+[100,150,250,500]:
        r0=u//2+1;W=3*r0
        for alpha in [1,2,u+r0]:
            F=arm_prefix(alpha,[2]*u+[3]*r0,alpha+2*u+3*r0+1)
            for n in range(r0+3,len(F)-1):assert F[n]**2>=F[n-1]*F[n+1];ct['EXACT_first_degree_crossing_ENTIRE_ordinary_LC_seed_minors']+=1
            ct['unbounded_seed_grammar_QA_hosts']+=1;sha.update(str((u,r0,alpha,F)).encode())
    out=dict(status='EXACT_QA_PASS_ALL_BINARY_TERNARY_ACTUAL_COMPLETE_C_AND_SHARP_ORDINARY_CLASSIFICATION_UNDER_PROOF_AUDIT',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      scope='QAONLY. ALLu/rproofusesANALYTICfirstdegreecrossingentranceforalllargeu+74COMPLETEfixedr6smallubases+unboundedappend3heredity. Sharpordinaryiffu<=2rforr>=6/u>=1;complementEXACT-4r. No originalgeneralUIclaim.')
    (ROOT/'audit_all_binary_ternary_complete_C.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
