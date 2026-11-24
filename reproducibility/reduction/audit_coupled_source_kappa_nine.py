"""Exact QA of closed-gap S-to-window A2 and the K=9 coefficient criterion."""
from pathlib import Path
from random import Random
from collections import Counter
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_binary_first_defect_ordinary_tail import arm
from audit_joint_structure import fastconv
from audit_mixed_binary_reference_ordinary import full_C
from verify_binary_ternary_A2_original_family import UI,core,greedy_ideal
def at(p,n):return p[n] if 0<=n<len(p) else 0
def interval(p,t):
    out=[];s=0
    for n in range(len(p)+t-1):s+=at(p,n)-at(p,n-t);out.append(s)
    return out
def A2(p):return UI([max(0,x-at(p,n-1))<<n for n,x in enumerate(p)])
def check_closed_source(p,t,ct):
    u=[max(0,x-at(p,n-1)) for n,x in enumerate(p)]
    a2=[x<<n for n,x in enumerate(u)];ell=a2.index(max(a2));m=len(p)-1-p[::-1].index(max(p))
    E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
    for n in range(max(m+1,t),len(p)):
        k=n-t
        if k>=ell or at(p,n)<=at(p,k) or at(p,n+1)<=at(p,k+1):continue
        if 0<=E[n]<=E[k]:
            ct['tested_closed_proper_source_comparisons']+=1
            if E[n]==E[k]:ct['closed_EQUAL_source_comparisons']+=1
            if E[n+1]-E[n]>E[k+1]-E[k]:return False
    return True
def main():
    st=time.monotonic();ct=Counter();rng=Random(9918742);sha=hashlib.sha256()
    for _ in range(1800):
        increments=sorted(rng.randint(1,15) for _ in range(rng.randint(1,10)))
        p=[1]
        for u in increments:p.append(p[-1]+u)
        p += [p[-1]]*rng.randint(0,4)
        for _ in range(rng.randint(2,12)):p.append(rng.randint((p[-1]+1)//2,p[-1]))
        assert UI(p) and A2(p) and UI([x<<n for n,x in enumerate(p)])
        for t in [2,3,5,8,13]:
            if check_closed_source(p,t,ct):
                assert A2(interval(p,t));ct['generic_closed_S_FULL_window_A2_implications']+=1
            else:ct['generic_source_hypothesis_failures']+=1
    small=json.loads((ROOT/'kappa_nine_head_certificate_data.json').read_text(encoding='utf8'))
    owners={(r['alpha'],tuple(r['U'])) for r in small['exceptions']}
    owners |= {(1,(2,)),(1,(3,)),(2,(3,)),(1,(2,2)),(1,(2,3)),(2,(2,2))}
    for alpha,U in sorted(owners):
        X=arm(alpha,list(U))[:-2]
        for beta,h in [(1,7),(1,8),(3,10)]:
            V=[8]*h;Y=arm(beta,V)[:-2];K=9;D=len(X)+len(Y)-2
            full_C(Y+[0,0],len(Y),ct,'actual_K9_opposite')
            p=fastconv(X[::-1],Y[::-1]);assert A2(p)
            E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
            nu=len(p)-1-p[::-1].index(max(p))
            for n in range(nu+1,len(p)):
                if E[n]>=0 and E[n+1]>E[n]:
                    assert D-n<=10;ct['actual_all_positive_Q_recoveries_j_at_most_ten']+=1
            for t in range(1,15):
                assert check_closed_source(p,t,ct) and A2(interval(p,t))
                ct['actual_K9_ALL_short_and_long_weighted_windows']+=1
            ct['actual_K9_exception_owner_pairs']+=1
            sha.update(str((alpha,U,beta,V,p,E)).encode())
    def profile(jumps):
        a=rng.randint(1,6);u=rng.randint(0,10)
        V=[3]*rng.randint(0,3)+[4]*rng.randint(0,3)
        for _ in range(jumps):V.append(max(5,2*sum(V))+rng.randint(0,3))
        return a,[2]*u+V
    for j in range(320):
        a,U=profile(j%5);b,V=profile(j//5%5);X,Y=arm(a,U)[:-2],arm(b,V)[:-2]
        p=fastconv(X[::-1],Y[::-1]);assert A2(p)
        for F in [X,Y]:full_C(F+[0,0],len(F),ct,'A15_actual_arm')
        for t in [3,4,5,6,9,14]:
            assert check_closed_source(p,t,ct) and A2(interval(p,t));ct['actual_A15_FULL_weighted_window_A2']+=1
        for aa,UU,F,G in [(a,U,X,Y),(b,V,Y,X)]:
            t=max(max(UU+[2]),len(G)-len(F),2)
            T=arm(aa,UU+[t])[:-2];q=fastconv(T[::-1],G[::-1]);assert A2(q)
            ct['arbitrary_legal_heavier_append_FULL_A2_pairs']+=1
        ct['actual_A15_FULL_A2_pairs']+=1
    for j in range(12):
        a,b=1+j%2,1+j%3;U=[2]*(j%3)+[3]+[4]*(1+j%2);V=[2]*(j%4)+[3]*(1+j%2)+[4]
        for Q in [U,V]:
            for _ in range(4):Q.append(max(5,2*sum(v for v in Q if v>=3)))
        if j%4==0:
            if a+sum(U)<b+sum(V):a,b,U,V=b,a,V,U
            U=U+[max(U)+1];ct['extra_heavier_append_ORIGINAL_ideals']+=1
        M=max(U+V)+1;X,Y=arm(a,U)[:-2],arm(b,V)[:-2];H,L,R=core(X,Y,M)
        host=[1]*a+U+[M]+list(reversed([1]*b+V));actual=greedy_ideal(host)
        assert actual==H and all(UI(q) for q in [actual,L,R])
        ct['TRUE_greedy_BOTH_four_dominant_ORIGINAL_ideals']+=1;ct['TRUE_greedy_ORIGINAL_rank_counts']+=len(actual)
        ct['BOTH_relative_polynomials']+=2
        sha.update(str((host,actual)).encode())
    out=dict(status='PASS_EXACT_QA_CLOSED_SOURCE_WINDOW_A2_AND_KAPPA_NINE_ORIGINAL',counts=dict(ct),
        state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
        scope='FiniteQAONLY;COMPLETE406rank/2143owner/4377inputcertificateisexplicitNEWfinitepremise. WHOLEweightedwindowA2doesNOTassertwholeRAWsourcewindowUI;GENERALoriginalOPEN.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
