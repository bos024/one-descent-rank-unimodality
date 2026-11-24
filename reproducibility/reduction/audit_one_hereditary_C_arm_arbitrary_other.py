"""Independent actual-coefficient QA, not a finite premise for the theorem."""
from pathlib import Path
from collections import Counter
from random import Random
import sys,json,hashlib,time,gc
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE));sys.set_int_max_str_digits(0)
from audit_first_missing_twelve_original import fast_core,fast_greedy,weighted_D_UI
from probe_binary_first_defect_ordinary_tail import arm
from verify_subdegree_CI_entrance import suffix_boxes
from verify_binary_ternary_A2_original_family import greedy_ideal,conv,UI

def at(p,n):return p[n] if 0<=n<len(p) else 0
def full_C(A):
    G=[];s=0
    for x in A:s+=x;G.append(s)
    D=[0,0]+[max(0,A[n]-A[n-1]) for n in range(2,len(A))]
    return all(G[k+1]*D[n]>=G[k]*D[n+1] for n in range(2,len(A)-1)
               if D[n]*D[n+1]>0 for k in range(n-2))
def marked_family(rng,i):
    a=rng.randint(1,7)
    if i%4==0:return a,sorted(rng.choices(range(2,43),k=rng.randint(0,5))),'five_arbitrary'
    if i%4==1:return a,sorted(rng.choices(range(2,5),k=rng.randint(6,25))),'capacity_four'
    if i%4==2:return a,[2]*rng.randint(0,20)+sorted(rng.choices(range(3,36),k=2)),'two_nonbinary'
    U=[2]*rng.randint(0,7)+[3,4]
    for _ in range(2):U.append(2*sum(t for t in U if t>=3))
    return a,U,'dominant_tower'

def main():
    outdir=Path(__file__).resolve().parent;start=time.monotonic();rng=Random(720261102)
    ct=Counter();sha=hashlib.sha256();cases=[]
    for _ in range(15):
        host=[rng.randint(1,6) for _ in range(rng.randint(1,7))]
        assert fast_greedy(host)==greedy_ideal(host);ct['independent_letter_DP_controls']+=1
    for i in range(120):
        a,U,label=marked_family(rng,i)
        b=rng.randint(1,6);V=sorted(rng.choices(range(5,25),k=rng.randint(6,20)))
        cases.append((a,U,b,V,label,False))
        if i%5==0:
            t=max(max(U or [1]),b+sum(V)-a-sum(U),2)+rng.randint(0,4)
            cases.append((a,U+[t],b,V,label,True))
    cases.extend([(1,[2]*20,1,[6]*402+[7]*68,'ordinary_LC_obstruction',False),
                  (2,[3,4,7,9,11],1,[5,5,5,6,6,7,7],'both_nonbinary_mass_above_32',False)])
    for serial,(a,U,b,V,label,extra) in enumerate(cases):
        A=arm(a,U)[:-2];B=arm(b,V)[:-2]
        assert A==suffix_boxes(a,U)[:len(A)] and B==suffix_boxes(b,V)[:len(B)]
        ct['independent_suffix_box_arm_counts']+=2
        if not extra:assert full_C(A);ct['marked_current_FULL_C_QA']+=1
        else:assert full_C(arm(a,U[:-1])[:-2]) and a+sum(U)>=b+sum(V)
        M=max(U+V+[1])+rng.choice([1,2,7]);H,L,R=fast_core(A,B,M)
        host=[1]*a+U+[M]+list(reversed([1]*b+V));actual=fast_greedy(host)
        assert actual==H and all(UI(p) for p in [actual,L,R])
        p=conv(A[::-1],B[::-1]) if len(A)*len(B)<120000 else None
        if p is None:
            from audit_joint_structure import fastconv
            p=fastconv(A[::-1],B[::-1])
        assert weighted_D_UI(p);ct['FULL_A2_products']+=1
        ct['TRUE_leftmost_embedding_originals']+=1;ct['BOTH_relative_polynomials']+=2
        ct['original_coefficient_ranks']+=len(H);ct[label]+=1
        if extra:ct['arbitrary_marked_heavier_extra_appends']+=1
        if serial<30:
            P=conv(A,B);expected=[sum(at(P,n-i) for i in range(1,M+1))-at(P,n)+at(A,n)+at(B,n) for n in range(len(P)+M)]
            assert H==expected;ct['independent_naive_original_core_identities']+=1
        if not extra:
            P=p[::-1]
            EA=[(1 if n==0 else -1 if n==1 else 0)+2*at(A,n-1)-at(A,n) for n in range(len(A)+2)]
            EB=[(1 if n==0 else -1 if n==1 else 0)+2*at(B,n-1)-at(B,n) for n in range(len(B)+2)]
            from audit_joint_structure import fastconv
            EP=fastconv(EA,EB)
            for n in range(3,min(len(A),len(B))):
                e=2*at(P,n-1)-at(P,n)
                if e>=0:continue
                wa=at(EA,n)-at(EA,n-1);wb=at(EB,n)-at(EB,n-1)
                assert at(EP,n)<=wa and wa>=0 and wb>=0
                assert e-2*(2*at(P,n-2)-at(P,n-1))>=wb
                ct['negative_current_marked_source_budgets']+=1
        if label=='ordinary_LC_obstruction':
            assert B[472]**2-B[471]*B[473]<0
            assert B[472]>B[471] and B[472]-B[471]>B[471]-B[470]
            ct['arbitrary_other_violates_count_plus_two_LC']+=1
        sha.update(repr((a,U,b,V,M,H,L,R,p)).encode())
        if serial%30==0 or label=='ordinary_LC_obstruction':
            print(json.dumps(dict(case=serial,label=label,ranks=len(H),seconds=time.monotonic()-start)),flush=True)
        del A,B,H,L,R,p,actual;gc.collect()
    out=dict(status='PASS_QA_ONE_HEREDITARY_C_ARM_ARBITRARY_OTHER_ORIGINAL',formal_reports=0,
      scope='Finite QA ONLY. The unbounded proof uses the marked-pair deletion induction and frozen kernels. True leftmost-embedding original counts do not use arm recurrences or core identities.',
      counts=dict(ct),sha256=sha.hexdigest(),seconds=time.monotonic()-start,
      general_C='OPEN',general_A2='OPEN',general_original='OPEN')
    (outdir/'audit_one_hereditary_C_arm_arbitrary_other.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)
if __name__=='__main__':main()
