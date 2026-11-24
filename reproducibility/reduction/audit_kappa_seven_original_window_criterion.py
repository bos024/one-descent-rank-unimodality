"""Finite exact QA only. New finite proof premise is the COMPLETE owner table."""
from pathlib import Path
from collections import Counter
from random import Random
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_binary_first_defect_ordinary_tail import arm
from audit_mixed_binary_reference_ordinary import full_C
from audit_joint_structure import fastconv
from verify_binary_ternary_A2_original_family import core,greedy_ideal,UI

def at(a,n):return a[n] if 0<=n<len(a) else 0
def window(a,t):
    out=[];v=0
    for n in range(len(a)+t-1):v+=at(a,n)-at(a,n-t);out.append(v)
    return out
def profile(rng,kind):
    a=rng.randint(1,6);u=rng.randint(0,18)
    if kind<3:
        V=[3]*rng.randint(0,5)+[4]*rng.randint(0,5)
        for j in range(kind):V += [max(5,2*sum(V))+rng.randint(0,5)]
    else:
        V=sorted(rng.choices([3,4,5,6],k=rng.randint(1,5)))
        assert sum(V)<=32
    return a,[2]*u+V
def small_kind(a,U):
    if (a,U)==(1,[2]):return 'onepart3'
    if (a,U) in [(1,[3]),(2,[2])]:return 'onepart4'
    if (a,U)==(1,[2,2]):return 'binary2'
    if (a,U)==(1,[2,2,2]):return 'binary3'
    return None
def main():
    st=time.monotonic();rng=Random(710941);ct=Counter();sha=hashlib.sha256()
    cases=[(profile(rng,j%4),profile(rng,j//4%4)) for j in range(1200)]
    cases += [((a,U),(b,[6]*r)) for a,U in [(1,[2]),(1,[3]),(2,[2]),(1,[2,2]),(1,[2,2,2])]
        for b in [1,2,9] for r in [5,6,7,8]]
    for (alpha,U),(beta,V) in cases:
        A,B=arm(alpha,U)[:-2],arm(beta,V)[:-2];a,b=len(A)-1,len(B)-1
        ka=next(n for n in range(1,9) if at(A,n)<2**(n-1));kb=next(n for n in range(1,9) if at(B,n)<2**(n-1))
        assert max(ka,kb)<=7
        full_C(A+[0,0],len(A),ct,'kappa_seven_single_arm')
        full_C(B+[0,0],len(B),ct,'kappa_seven_single_arm')
        p=fastconv(A[::-1],B[::-1]);D=len(p)-1
        E=[2*at(p,n)-at(p,n-1) for n in range(D+3)]
        d=[max(0,v-at(p,n-1)) for n,v in enumerate(p)];assert UI([v<<n for n,v in enumerate(d)])
        ct['actual_class_FULL_A2_pairs']+=1
        expected=[];tag=None
        for aa,UU,kk,other,weight in [(alpha,U,kb,B,b),(beta,V,ka,A,a)]:
            kind=small_kind(aa,UU)
            if kk==6 and kind=='onepart3':expected=[weight-1];tag='old_six'
            if kk==7 and kind in ['onepart3','onepart4']:expected=[weight-1];tag=kind
            if kk==7 and kind=='binary2':expected=[weight];tag=kind
            if kk==7 and kind=='binary3':
                eta=2*at(other,7)-at(other,8)
                if eta==1:expected=[weight];tag=kind
        if U and V:
            nu=D-p[::-1].index(max(p))
            bad=[n for n in range(nu+1,len(E)-1) if E[n]>=0 and E[n+1]>E[n]]
            assert bad==expected,(alpha,U,beta,V,bad,expected)
            if tag:ct['exact_source_exception_'+tag]+=1
            for t in [4,5,6,11,37]:
                W=window(E,t);assert UI([max(0,v) for v in W]);ct['four_or_longer_source_windows']+=1
        for olda,oldU,oppA,opp in [(alpha,U,B,V),(beta,V,A,U)]:
            F=arm(olda,oldU)[:-2];t=max(max(oldU+[2]),len(oppA)-len(F),2)
            if U and V:assert UI([max(0,v) for v in window(E,t)])
            X=arm(olda,oldU+[t])[:-2];q=fastconv(X[::-1],oppA[::-1]);dd=[max(0,v-at(q,n-1)) for n,v in enumerate(q)]
            assert UI([v<<n for n,v in enumerate(dd)]);ct['legal_heavier_append_FULL_A2_pairs']+=1
        sha.update(str((alpha,U,beta,V,E)).encode())
    for j in range(24):
        a,b=1+j%3,1+j%2
        U=[2]*(j%5)+[3]*(1+j%2)+[4]*(1+j%2)
        V=[2]*(j%3)+[3]*(1+(j+1)%2)+[4]*(1+j%3)
        for W in [U,V]:
            W.append(max(5,2*sum(t for t in W if t>=3)))
            W.append(2*sum(t for t in W if t>=3))
        if j%6==0:
            if a+sum(U)<b+sum(V):a,b,U,V=b,a,V,U
            U=U+[max(U)+1];ct['extra_heavier_append_ORIGINAL_ideals']+=1
        M=max(U+V)+1;X,Y=arm(a,U)[:-2],arm(b,V)[:-2];H,L,R=core(X,Y,M)
        host=[1]*a+U+[M]+list(reversed([1]*b+V));actual=greedy_ideal(host)
        assert actual==H and UI(actual)
        ct['TRUE_greedy_BOTH_two_dominant_ORIGINAL_ideals']+=1
        ct['TRUE_greedy_ORIGINAL_rank_counts']+=len(actual)
        sha.update(str((host,actual)).encode())
    A,B=arm(1,[2])[:-2],arm(1,[6]*5)[:-2];p=fastconv(A[::-1],B[::-1]);E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
    b=len(B)-1;assert window(E,3)[b-1:b+2]==[3,1,2]
    out=dict(status='PASS_EXACT_QA_KAPPA_SEVEN_LEGAL_WINDOW_COEFFICIENT_CRITERION',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
        scope='Finite QA ONLY. Complete341-owner table is NEWfiniteproofpremise, separatelykernelcheckedandneedsindependentreconstruction. General original conjecture OPEN.')
    (ROOT/'audit_kappa_seven_original_window_criterion.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
