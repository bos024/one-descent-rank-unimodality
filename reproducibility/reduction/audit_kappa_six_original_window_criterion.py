"""Exact QA only for the proposed analytic kappa-six coefficient criterion."""
from pathlib import Path
from random import Random
from collections import Counter
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_binary_first_defect_ordinary_tail import arm
from audit_joint_structure import fastconv
from verify_binary_ternary_A2_original_family import core,greedy_ideal,UI
from audit_mixed_binary_reference_ordinary import full_C

def at(a,n):return a[n] if 0<=n<len(a) else 0
def window(a,t):
    out=[];v=0
    for n in range(len(a)+t-1):v+=at(a,n)-at(a,n-t);out.append(v)
    return out
def profile(rng,kind):
    alpha=rng.randint(1,7);u=rng.randint(0,24)
    if kind==0:V=[3]*rng.randint(0,8)+[4]*rng.randint(0,8)
    elif kind==1:
        V=[3]*rng.randint(0,4)+[4]*rng.randint(0,4)
        V += [max(5,2*sum(V))+rng.randint(0,7)]
    else:
        V=sorted(rng.choices([3,4,5],k=rng.randint(1,6)))
        assert sum(V)<=32
    return alpha,[2]*u+V
def main():
    st=time.monotonic();rng=Random(688721);ct=Counter();sha=hashlib.sha256()
    cases=[(profile(rng,i%3),profile(rng,i//3%3)) for i in range(1000)]
    cases += [((1,[2]),(a,[5]*k)) for a in [1,2,7,25] for k in [4,5,6]]
    originals=[]
    for j,((alpha,U),(beta,V)) in enumerate(cases):
        A,B=arm(alpha,U)[:-2],arm(beta,V)[:-2];a,b=len(A)-1,len(B)-1
        ka=next(n for n in range(1,8) if at(A,n)<2**(n-1))
        kb=next(n for n in range(1,8) if at(B,n)<2**(n-1));assert max(ka,kb)<=6
        full_C(A+[0,0],len(A),ct,'class_single_arm')
        full_C(B+[0,0],len(B),ct,'class_single_arm')
        p=fastconv(A[::-1],B[::-1]);D=len(p)-1;E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
        d=[max(0,x-at(p,n-1)) for n,x in enumerate(p)]
        assert UI([x<<n for n,x in enumerate(d)]);ct['actual_class_FULL_A2_pairs']+=1
        special=b if (alpha,U)==(1,[2]) and kb==6 else a if (beta,V)==(1,[2]) and ka==6 else None
        nonrect=bool(U and V)
        if nonrect:
            nu=D-p[::-1].index(max(p));bad=[]
            for n in range(nu+1,len(E)-1):
                if E[n]>=0 and E[n+1]>E[n]:bad.append(n)
                ct['whole_post_LAST_mode_Q_comparisons']+=1
            if special is None:
                assert not bad and UI([max(0,x) for x in E])
                ct['normal_entire_raw_source_cones']+=1
            else:
                assert bad==[special-1]
                assert E[special-1:special+5]==[0,1,1,-1,0,-1]
                assert min(E[:special-1])>=1 and UI(E[:special-1])
                assert nu<=special-3
                ct['complete_exceptional_source_classifications']+=1
            for t in [3,4,5,8,31]:
                W=window(E,t);assert UI([max(0,x) for x in W])
                ct['ALL_positive_three_or_longer_source_windows']+=1
        # Legal heavier append: source property at t=2 is needed only when
        # it is actually legal and heavy; the exceptional pair cannot use it.
        t0=max(max(U+[2]),b-a,2)
        if special is not None:assert t0>=3
        for t in sorted(set([t0,t0+1,t0+7])):
            if nonrect:
                W=window(E,t);assert UI([max(0,x) for x in W]);ct['legal_heavier_append_source_windows']+=1
            X=arm(alpha,U+[t])[:-2];q=fastconv(X[::-1],B[::-1]);dd=[max(0,x-at(q,n-1)) for n,x in enumerate(q)]
            assert UI([x<<n for n,x in enumerate(dd)]);ct['legal_heavier_append_FULL_A2']+=1
        if j%20==0 or special is not None:originals.append((alpha,U,beta,V))
        sha.update(str((alpha,U,beta,V,E,d)).encode())
    for alpha,U,beta,V in originals:
        A,B=arm(alpha,U)[:-2],arm(beta,V)[:-2];M=max([1]+U+V)+1
        H,L,R=core(A,B,M);host=[1]*alpha+U+[M]+list(reversed([1]*beta+V))
        actual=greedy_ideal(host);assert actual==H and UI(actual)
        ct['TRUE_greedy_ORIGINAL_kappa_six_class_pairs']+=1
        ct['TRUE_greedy_ORIGINAL_rank_counts']+=len(actual)
        sha.update(str((host,actual)).encode())
    out=dict(status='PASS_EXACT_QA_KAPPA_SIX_LEGAL_WINDOW_COEFFICIENT_CRITERION',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
        scope='Finite QA ONLY. Criterion theorem still under written/Lean audit; no whole raw-source UI at kappa6 asserted. General conjecture OPEN.')
    (ROOT/'audit_kappa_six_original_window_criterion.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
