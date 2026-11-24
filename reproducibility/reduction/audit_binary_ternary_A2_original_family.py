"""Exact QA only; the unbounded A2 and ORIGINAL family proofs are analytic."""
from pathlib import Path
from collections import Counter
from random import Random
import sys,json,hashlib,time
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_joint_structure import fastconv

def at(p,n):return p[n] if 0<=n<len(p) else 0
def UI(p):
    down=False
    for a,b in zip(p,p[1:]):
        if b<a:down=True
        elif b>a and down:return False
    return True
def window(p,t):
    out=[];v=0
    for n in range(len(p)+t-1):v+=at(p,n)-at(p,n-t);out.append(v)
    return out
def arm(a,U):return arm_prefix(a,U,a+sum(U))
def examine(A,B,ct,sha,nonrect):
    p=fastconv(A[::-1],B[::-1]);D=len(p)-1
    d=[max(0,x-at(p,n-1)) for n,x in enumerate(p)]
    E=[2*at(p,n)-at(p,n-1) for n in range(D+3)]
    assert UI([x<<n for n,x in enumerate(d)])
    ct['actual_FULL_A2_pairs']+=1
    for n in range(D):
        assert (2*d[n+1]-d[n])==E[n+1]-E[n] or p[n+1]<p[n] or p[n]<at(p,n-1)
    if nonrect:
        assert UI([x<<n for n,x in enumerate(p)]) and UI([max(0,x) for x in E])
        sup=[n for n,x in enumerate(E) if x>0];assert sup==list(range(sup[-1]+1))
        m=D-p[::-1].index(max(p))
        for n in range(m+1,D+2):
            if E[n]>=0:assert E[n+1]<=E[n];ct['actual_Q_guarded_tail_edges']+=1
        for t in [2,3,4,7,31]:
            W=window(E,t);assert UI([max(0,x) for x in W]);ct['ENTIRE_signed_source_windows']+=1
        ct['actual_A1_and_ENTIRE_positive_source_hosts']+=1
    sha.update(str((A,B,p,d,E)).encode())

def main():
    st=time.monotonic();rng=Random(2026110181);ct=Counter();sha=hashlib.sha256()
    triples=[(a,u,r) for a in [1,2,9] for u in range(4) for r in range(4)]
    cases=[(x,y) for i,x in enumerate(triples) for y in triples[i:]]
    cases += [((rng.randint(1,150),rng.randint(0,60),rng.randint(0,60)),
               (rng.randint(1,150),rng.randint(0,60),rng.randint(0,60))) for _ in range(700)]
    for x,y in cases:
        a,u,r=x;b,v,s=y;A=arm(a,[2]*u+[3]*r);B=arm(b,[2]*v+[3]*s)
        examine(A,B,ct,sha,bool(u+r and v+s))
        if ct['actual_FULL_A2_pairs']%13:continue
        for M in [max(([3] if r+s else [2] if u+v else [1]))+1,17]:
            if M<=max([1]+[2]*(u+v)+[3]*(r+s)):continue
            core_rel(A,B,M,ct,sha,'B3')
    for _ in range(500):
        a,b=rng.randint(1,150),rng.randint(1,150)
        u,r,v,s=[rng.randint(0,35) for _ in range(4)]
        Z=arm(a,[2]*u+[3]*r);B=arm(b,[2]*v+[3]*s)
        t=max(4,rng.randint(4,300),len(B)-len(Z));A=[1]+window(Z,t)
        assert len(A)>=len(B)
        examine(A,B,ct,sha,False)
        for M in [t+1,t+2,t+19]:core_rel(A,B,M,ct,sha,'heavier_arbitrary_jump')
    def extended_arm(kind):
        a=rng.randint(1,100)
        if kind==0:U=[2]*rng.randint(0,35)+[3]*rng.randint(0,35)
        elif kind==1:U=[2]*rng.randint(0,70)+[rng.randint(2,150)]
        else:U=sorted(rng.randint(2,100) for _ in range(rng.randint(0,2)))
        return a,U
    for i in range(600):
        a,U=extended_arm(i%3);b,V=extended_arm((i//3)%3)
        A,B=arm(a,U),arm(b,V);examine(A,B,ct,sha,bool(U and V))
        maximum=max([1]+U+V)
        core_rel(A,B,maximum+1,ct,sha,'expanded_A4')
        t=max(U+[2])+rng.randint(0,150)
        t=max(t,len(B)-len(A));X=[1]+window(A,t)
        assert len(X)>=len(B)
        examine(X,B,ct,sha,False)
        core_rel(X,B,max(t,maximum)+1,ct,sha,'expanded_A4_heavier_append')
    out=dict(status='EXACT_QA_PASS_BINARY_TERNARY_FULL_A2_AND_ORIGINAL_FAMILY_UNDER_PROOF_AUDIT',
      counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      scope='Finite diagnostics ONLY. Full analytic proof usesALLB3C+OLDtwoNONBINARYC=>A4C/kappa<=4=>A1/Q;FULLoldA2=>ENTIREsignedsourcecone=>ANYsignedwindow=>NEWFULLA2. A4=B3 ORbinary-plus-one-arbitrary-tail ORat-most-two-arbitrary-nonones. ORIGINALcore/BOTHrelativesfollowbydeletionclosedleastpeakfamily,includingONEarbitraryheavierappendfromA4. ArbitrarycapacityGENERALoriginal/C/A2OPEN.')
    (ROOT/'audit_binary_ternary_A2_original_family.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)

def core_rel(A,B,M,ct,sha,kind):
    C=fastconv(A,B);W=[0]+window(C,M)
    L=[at(A,n)+at(W,n)-at(C,n) for n in range(len(W))]
    R=[at(B,n)+at(W,n)-at(C,n) for n in range(len(W))]
    H=[at(L,n)+at(B,n) for n in range(len(W))]
    assert min(L)>=0 and min(R)>=0 and min(H)>=0
    assert UI(H) and UI(L) and UI(R)
    ct[kind+'_ORIGINAL_cores']+=1;ct[kind+'_BOTH_relative_polynomials']+=2
    ct[kind+'_coefficient_comparisons']+=len(H)+len(L)+len(R)-3
    sha.update(str((kind,M,H,L,R)).encode())
if __name__=='__main__':main()
