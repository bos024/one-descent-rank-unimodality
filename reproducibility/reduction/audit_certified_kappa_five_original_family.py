"""Exact QA ONLY for the first-missing-five refinement and its sharp source counter."""
from pathlib import Path
from random import Random
from collections import Counter
import json,hashlib,time
from audit_binary_ternary_A2_original_family import arm,examine,core_rel,at
ROOT=Path(__file__).resolve().parent
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=Random(2026110185)
    def profile(kind):
        a=rng.randint(1,120);u=rng.randint(0,50)
        if kind==0:U=[2]*u+[3]*rng.randint(0,50)
        elif kind==1:U=[2]*u+sorted(rng.randint(3,150) for _ in range(rng.randint(0,2)))
        else:
            r=rng.randint(1,40);U=[2]*u+[3]*r+[rng.randint(6*r,6*r+200)]
        return a,U
    for case in range(1200):
        a,U=profile(case%3);b,V=profile(case//3%3);A,B=arm(a,U),arm(b,V)
        for F,W in [(A,U),(B,V)]:
            if W:
                k=next(n for n in range(1,7) if at(F,n)<2**(n-1));assert 3<=k<=5
        examine(A,B,ct,sha,bool(U and V))
        M=max([1]+U+V)+1;core_rel(A,B,M,ct,sha,'A5')
        if case%4==0:
            t=max(max(U+[2]),len(B)-len(A))+rng.randint(0,120)
            from audit_binary_ternary_A2_original_family import window
            X=[1]+window(A,t);assert len(X)>=len(B)
            examine(X,B,ct,sha,False);core_rel(X,B,max(M-1,t)+1,ct,sha,'A5_arbitrary_heavier_append')
    A=arm(1,[2]);B=arm(1,[5]*4)
    from audit_joint_structure import fastconv
    P=fastconv(A,B);p=P[::-1];E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
    assert P[3:7]==[9,17,34,65] and E[19:22]==[3,0,1]
    out=dict(status='EXACT_QA_PASS_CERTIFIED_KAPPA_FIVE_ORIGINAL_FAMILY_AND_SHARP_SOURCE_BOUND',
      counts=dict(ct),sharp_actual_source_counter=dict(X=[1,2],Y=[1]+[5]*4,kappaX=3,kappaY=6,forward_P3_to_P6=P[3:7],raw_E19_to_E21=E[19:22]),
      state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,scope='Finite QA ONLY. Universal analytic proof reusesFULLC/OLDgap5mixed+onepartflatprimitive/birthrankZERO+OLDsourcecone/window/A2/leastpeakassemblies. GENERALoriginal/C/A2OPEN. ExactsourcecounterdoesNOTrefuteA2/originalUI.')
    (ROOT/'audit_certified_kappa_five_original_family.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
