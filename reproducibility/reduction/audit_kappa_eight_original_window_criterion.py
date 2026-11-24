"""Finite exact QA; the separate COMPLETE owner table is the only new finite premise."""
from pathlib import Path
from random import Random
from collections import Counter
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_binary_first_defect_ordinary_tail import arm
from audit_mixed_binary_reference_ordinary import full_C
from audit_joint_structure import fastconv
from verify_binary_ternary_A2_original_family import UI,core,greedy_ideal
def at(p,n):return p[n] if 0<=n<len(p) else 0
def window(p,t):
    out=[];v=0
    for n in range(len(p)+t-1):v+=at(p,n)-at(p,n-t);out.append(v)
    return out
def small_profiles():
    return [(1,[2]),(1,[3]),(1,[4]),(2,[3]),(1,[2,2]),(1,[2,3]),(2,[2,2]),
        (1,[2,2,2]),(1,[2,2,3]),(2,[2,2,2])]
def main():
    st=time.monotonic();rng=Random(880391);ct=Counter();sha=hashlib.sha256()
    opposites=[(a,[7]*h) for a in [1,2,8] for h in [6,7,8,9,12]]
    opposites += [(a,[2]*u+list(range(3,8))) for a in [1,3] for u in [1,2,9]]
    for alpha,U in small_profiles():
        X=arm(alpha,U)[:-2];a=len(X)-1
        for beta,V in opposites:
            Y=arm(beta,V)[:-2];b=len(Y)-1
            assert next(n for n in range(1,10) if at(Y,n)<2**(n-1))==8
            full_C(Y+[0,0],len(Y),ct,'actual_kappa_eight_opposite')
            delta=128-Y[8];eta=2*Y[8]-Y[9];zeta=2*Y[9]-Y[10]
            assert 1<=delta<=eta and zeta>=eta+1
            p=fastconv(X[::-1],Y[::-1]);D=len(p)-1
            E=[2*at(p,n)-at(p,n-1) for n in range(D+3)]
            d=[max(0,v-at(p,n-1)) for n,v in enumerate(p)];assert UI([v<<n for n,v in enumerate(d)])
            if len(U)==1:
                m=min(alpha+1,U[0]);L=b+a-7;R=b+m-1;B=L;H=1
                critical=[0]*(b-L-1)+[1]*m
            elif len(U)==2:
                L=b+a-7;R=b+(1 if a==5 else 2);B=L-1;H=2
                critical=([0,1,2] if a==5 else [1,2,1])
                assert E[L-1]==delta+eta
            elif a==7:
                if delta>=2:
                    assert UI([max(0,x) for x in E]);ct['three_part_no_exception_delta_paid']+=1;continue
                L=b-1;R=b+2;B=L-1;H=3;critical=[2,3,2]
                assert E[L]==delta+eta and E[L-1]==zeta+eta+2*delta
            else:
                if eta>=2:
                    assert UI([max(0,x) for x in E]);ct['three_part_no_exception_eta_paid']+=1;continue
                assert delta==eta==1
                L=b-1;R=b+3;B=L;H=4;critical=[3,4,3,1 if alpha==1 else 0]
                assert E[L]==zeta+3
            assert E[L+1:R+1]==critical,(alpha,U,beta,V,E[L+1:R+1],critical)
            assert min(E[:L+1])>=1 and UI(E[:L+1]) and min(E[1:B+1])>=H
            assert max(E[R+1:],default=0)<=0
            nu=D-p[::-1].index(max(p));assert nu<L
            for t in sorted(set([5,6,7,17,max(5,b-a),b,b+1])):
                assert R<=t+B
                W=window(E,t);assert UI([max(0,x) for x in W]);ct['entire_exceptional_five_window_repairs']+=1
            ct['entire_source_profile_types_'+str((alpha,U))]+=1
            sha.update(str((alpha,U,beta,V,L,R,B,H,E)).encode())
    def profile(kind):
        a=rng.randint(1,5);u=rng.randint(0,12)
        if kind<4:
            V=[3]*rng.randint(0,3)+[4]*rng.randint(0,3)
            for _ in range(kind):V.append(max(5,2*sum(V))+rng.randint(0,2))
        else:
            V=sorted(rng.choices([3,4,5,6,7],k=rng.randint(1,4)));assert sum(V)<=32
        return a,[2]*u+V
    for j in range(500):
        a,U=profile(j%5);b,V=profile(j//5%5);X,Y=arm(a,U)[:-2],arm(b,V)[:-2]
        for F in [X,Y]:full_C(F+[0,0],len(F),ct,'A14_actual_arm')
        p=fastconv(X[::-1],Y[::-1]);E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
        d=[max(0,v-at(p,n-1)) for n,v in enumerate(p)];assert UI([v<<n for n,v in enumerate(d)])
        if U and V:
            for t in [5,7,13,29]:assert UI([max(0,x) for x in window(E,t)]);ct['general_A14_five_or_longer_windows']+=1
        for aa,UU,F,G in [(a,U,X,Y),(b,V,Y,X)]:
            t=max(max(UU+[2]),len(G)-len(F),2)
            if U and V:assert UI([max(0,x) for x in window(E,t)])
            T=arm(aa,UU+[t])[:-2];q=fastconv(T[::-1],G[::-1])
            d=[max(0,x-at(q,n-1)) for n,x in enumerate(q)];assert UI([x<<n for n,x in enumerate(d)])
            ct['legal_heavier_append_FULL_A2_pairs']+=1
        ct['actual_A14_FULL_A2_pairs']+=1
    for j in range(18):
        a,b=1+j%2,1+j%3
        U=[2]*(j%3)+[3]*(1+j%2)+[4]*(1+j%2)
        V=[2]*(j%4)+[3]*(1+(j+1)%2)+[4]*(1+j%2)
        for Q in [U,V]:
            for _ in range(3):Q.append(max(5,2*sum(v for v in Q if v>=3)))
        if j%6==0:
            if a+sum(U)<b+sum(V):a,b,U,V=b,a,V,U
            U=U+[max(U)+1];ct['extra_heavier_append_ORIGINAL_ideals']+=1
        M=max(U+V)+1;X,Y=arm(a,U)[:-2],arm(b,V)[:-2];H,L,R=core(X,Y,M)
        host=[1]*a+U+[M]+list(reversed([1]*b+V));actual=greedy_ideal(host)
        assert actual==H and UI(actual)
        ct['TRUE_greedy_BOTH_three_dominant_ORIGINAL_ideals']+=1;ct['TRUE_greedy_ORIGINAL_rank_counts']+=len(actual)
        sha.update(str((host,actual)).encode())
    X,Y=arm(1,[2])[:-2],arm(1,[7]*6)[:-2];p=fastconv(X[::-1],Y[::-1]);E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
    b=len(Y)-1;assert window(E,4)[b-1:b+2]==[3,1,2]
    out=dict(status='PASS_EXACT_QA_KAPPA_EIGHT_LEGAL_WINDOW_COEFFICIENT_CRITERION',counts=dict(ct),
        state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
        scope='AllfinitehostsQAONLY;COMPLETE1441owner/4457edge/694integercomplementisNEWexplicitfiniteproofpremise,nottheseopposites/originals. GeneraloriginalOPEN.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
