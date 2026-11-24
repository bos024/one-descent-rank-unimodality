"""Exact QA of the NEW u=h-1 multifactored CI proof route."""
from pathlib import Path
from collections import Counter
from itertools import accumulate
from random import Random
import hashlib,json,time
from audit_degree_boundary_CI_entrance import partitions,ci,Q,P,PSI,ZERO,LO,HI,DEN
from audit_joint_structure import fastconv
from audit_arbitrary_Fibonacci_tail_late_C import add,sub,mul,power,sign
from audit_binary_CI_infinite_padding_entrance import quotient,minor,convolution
from probe_divided_CI_positive_primitive import divided
from audit_padding_three_local_prefix import primitive,positive
from probe_finite_padding_geometric_deficit import arrays
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import rebuild
ROOT=Path(__file__).resolve().parent

def geometric_inverse(J):
    H=len(J)-1;X={H:ZERO}
    for n in range(H-1,-3,-1):X[n]=mul(Q,add(X[n+1],J[n+1] if n+1>=0 else ZERO))
    return X

def main():
    start=time.monotonic();ct=Counter();cert=set();small=[];startup=[];integer=set();sha=hashlib.sha256()
    def pay(x,key,finite=False):
        assert sign(x)>=0,(key,x);ct[key]+=1
        if finite:cert.add(x)
    for u in range(3,16):
        for ds in partitions(u+1):
            if len(ds)<2:continue
            V=[d+1 for d in ds];_,J=divided(ci(V),u);d=positive(primitive(J));X=geometric_inverse(J)
            for x in J:assert sign(x)>0;pay(x,'complete_small_positive_entries',True)
            for n in range(2,len(J)-1):pay(minor(J,n),'complete_small_ordinary_after_first_minors',True)
            for n in range(2,len(d)-1):pay(minor(d,n),'complete_small_later_primitive_minors',True)
            qb=sub(mul(Q,J[1]),J[0]);assert sign(qb)>0;pay(qb,'complete_small_inverse_first_centre_budget',True)
            small.append(dict(u=u,V=V))
            sha.update(json.dumps([u,V,J,d],separators=(',',':')).encode())
            if u+len(V)<8:
                for alpha in range(1,u+1):
                    W=sum(V);F=arm_prefix(alpha,[2]*u+V,alpha+2*u+W+5)
                    D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];ell=D.index(max(D));margins=[]
                    for n in range(W+1,ell):
                        z=D[n]**2-D[n-1]*D[n+1];assert z>=0
                        margins.append(z);integer.add(z);ct['complete_small_actual_startup_minors']+=1
                    startup.append(dict(u=u,V=V,alpha=alpha,first_mode=ell,margins=margins))
    assert len(small)==215 and len(startup)==17
    assert all(DEN*a+b*(LO if b>=0 else HI)>=0 for a,b in cert)
    _,J=divided([1]*6,4);d=positive(primitive(J));assert minor(d,3)==(4,-3) and sign(minor(d,3))<0
    _,J=divided(ci([3,3]),3);assert minor(J,1)==(62,-41) and sign(minor(J,1))<0
    # The NEW relaxed row zero is tested independently through every last centre.
    for u in range(16,76):
        QU=quotient(u)
        for s in range(2,u):
            pay(sub(QU[s],mul(power(Q,s),add((6*u+2,0),mul((4,0),Q)))),'relaxed_fourfold_row_zero')
    rng=Random(20261029766)
    for trial in range(1100):
        V=sorted(rng.choices(range(3,28),k=rng.randint(2,9)));h=sum(t-1 for t in V);u=h-1;L=ci(V);W=sum(V)
        E,J=divided(L,u);d=primitive(J);dp=positive(d);c=sub((1,0),J[0]);assert sign(c)<0 and sign(add(c,(1,0)))>0
        for x in J:assert sign(x)>0;ct['entire_subdegree_positive_entries']+=1
        for n in range(2,len(J)-1):pay(minor(J,n),'entire_subdegree_ordinary_after_first_minors')
        for n in range(2,len(dp)-1):pay(minor(dp,n),'entire_subdegree_later_primitive_minors')
        assert sign(sub(mul(Q,J[1]),J[0]))>0;ct['strict_inverse_initial_budget']+=1
        X=geometric_inverse(J)
        for n in range(-1,len(J)-1):pay(sub(mul(X[n],X[n]),mul(X[n-1],X[n+1])),'global_inverse_LC_including_initial_centre')
        _,C,_,_,_,_=arrays(V,u-1,1)
        assert X[-1]==(C[u-1]+1,0)
        for s in range(len(J)-1):assert X[s]==(C[u+s] if u+s<len(C) else 0,0)
        ct['exact_actual_extra_unit_inverse_alignment']+=1
        if u>=16:
            t=V[-1];old=V[:-1];r=len(old);QU=quotient(u)
            Qformal=QU+[mul((-1,0),mul(Q,QU[-1]))]
            B=convolution(Qformal,ci(old));a=mul(power(P,2),c);Y=[sub(B[n],mul(a,power(PSI,n))) for n in range(u+2)]
            for n in range(1,t):assert d[n]==Y[n]
            assert d[t]==sub(Y[t],(1,0)) and d[t+1]==sub(Y[t+1],B[1]);ct['exact_interval_primitive_identity']+=1
            if t<u:
                gap=sub(mul(B[1],Y[t-1]),mul((2,0),Y[t]));pay(sub(mul((40,0),gap),(u,0)),'uniform_subdegree_junction_gap')
            else:
                assert old==[3] and t==u
                assert d[u+1]==add((-u,0),mul(mul((2,0),Q),sub((1,0),power(PSI,u))))
                assert sign(d[u+1])<0;ct['exceptional_long_interval_negative_endpoint']+=1
        ref=rebuild(V,2*u+W+4);rd=[1]+[ref[n]-ref[n-1] for n in range(1,len(ref))]
        b,aa,dd=rd[W:W+3];assert dd==aa+b and sub((aa,0),mul(P,(b,0)))==c
        amp=b*b+aa*b-aa*aa;assert amp>0 and ref[W-1:W+1]==[aa,aa+b]
        ct['exact_reference_negative_conjugate_and_seed_geometry']+=1
        for alpha in {1,2,3,rng.randint(1,u),u+1,u+7}:
            N=alpha+2*u+W+5;F=arm_prefix(alpha,[2]*u+V,N)
            D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];ell=D.index(max(D));G=list(accumulate(F));best=1
            for n in range(W+1,ell):
                assert D[n]**2>=D[n-1]*D[n+1];ct['actual_subdegree_pre_mode_LC']+=1
            for n in range(4,len(F)):
                k=n-3
                if G[k]*G[best-1]<G[best]*G[k-1]:best=k
                if n>=W+1:
                    assert G[best]*D[n-1]>=G[best-1]*D[n];ct['all_actual_late_C_prefix_minimum']+=1
            delta=2 if alpha==1 else 1
            assert F[:W+1]==ref[:W+1] and D[W+1]==aa-delta
            seed=b*(aa+b)-(aa-delta)*aa
            assert seed==amp+delta*aa>0;ct['exact_positive_Cassini_single_seed_payment']+=1
            off=alpha-1
            for s in range(-1,len(J)-1):
                raw=sub(X[s],(E[s-off] if 0<=s-off<len(E) else 0,0))
                assert D[W+1+s]==max(0,raw[0]) and raw[1]==0
                ct['literal_actual_geometric_model_identification']+=1
            sha.update(json.dumps([V,u,alpha,J,X[-1],F,D],separators=(',',':')).encode());ct['actual_subdegree_contexts']+=1
    out=dict(status='EXACT_QA_PASS_SUBDEGREE_CI_REFINEMENT_UNDER_PROOF_AUDIT',counts=dict(ct),
        complete_small_contexts=small,complete_small_startup_contexts=startup,
        complete_small_scalar_margins=sorted(cert),complete_small_startup_integer_margins=sorted(integer),
        rational_root_interval=dict(lower=LO,upper=HI,denominator=DEN),
        single_factor_exclusion_control=dict(V=[6],u=4,primitive_centre=3,margin=[4,-3]),
        actual_multifactor_first_ordinary_minor_control=dict(V=[3,3],u=3,ordinary_centre=1,margin=[62,-41]),
        state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='Finite exact QA of a separate proposed UNBOUNDED proof for u=h-1,r>=2. All one-factor actual C already solved by prior theorem, not by this quotient assertion. Proof/formal/independent audits pending. General C/A2/original UI remain OPEN.')
    (ROOT/'audit_subdegree_CI_entrance.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if not k.startswith('complete_small')},ensure_ascii=False),flush=True)
    print(json.dumps(dict(complete_small_contexts=len(small),scalar_margins=len(cert),small_startups=len(startup),integer_margins=len(integer))),flush=True)

if __name__=='__main__':main()
