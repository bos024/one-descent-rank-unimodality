"""Exact actual C and original-coefficient QA; no finite premise in the proof."""
from pathlib import Path
from collections import Counter
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_binary_ternary_A2_original_family import arm,examine,core_rel,window,at
from probe_tribonacci_quadratic_inverse import ZERO,ONE,A,B,add,sub,mul,power,sign,pc
from build_tribonacci_rich_reverse_certificate import reverse
def sc(v,c):return tuple(c*x for x in v)
def app(F,t):return [1]+[sum(F[max(0,n-t):n]) for n in range(1,len(F))]
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256()
    for s in range(41):
        for extra in [0,7,25]:
            r=max(32,3*s+8)+extra;U=[3]*r+[4]*s;w=r+s
            for alpha in [1,2,3,5,11,40,120]:
                F=arm(alpha,U);Z=F+[0,0];G=[];v=0
                for x in Z:v+=x;G.append(v)
                d=[max(0,x-(Z[n-1] if n else 0)) if n>=2 else 0 for n,x in enumerate(Z)]
                for n in range(w+2,len(Z)-1):
                    assert Z[n]**2>=Z[n-1]*Z[n+1];ct['actual_ENTIRE_ordinary_tail_minors']+=1
                # Find the EXACT worst prefix cumulative ratio; no G-LC premise used.
                worst=1
                for N in range(4,len(Z)):
                    k=N-3
                    if G[k]*G[worst-1]<G[worst]*G[k-1]:worst=k
                    assert G[worst]*d[N-1]>=G[worst-1]*d[N],(alpha,r,s,N,worst)
                    ct['actual_complete_C_worst_prefix_checks']+=1
                    ct['actual_complete_C_logical_ALLshift_comparisons']+=k
                if s:assert F[5]<16
                ct['actual_complete_C_hosts']+=1
                sha.update(str((alpha,r,s,F[-4:])).encode())
    print(json.dumps(dict(phase='actual_C_ordinary_complete',counts=dict(ct))),flush=True)
    bsum=add(ONE,add(A,B));l=(0,1,0)
    for s,r in [(0,32),(1,32),(4,32),(8,32),(12,44),(22,74),(31,101),(45,143)]:
        E=[1]
        for t in [3]*r+[4]*s:E=pc(E,[1]*t)
        Q=reverse(E);R0=sub(ONE,Q[0]);R1=sub(sub((r+s,0,0),Q[1]),mul(A,Q[0]));Rs=add(R0,R1)
        P=r+s+2;NN=3*r+4*s+8;I=[1]*(NN+1)
        for t in [3]*r+[4]*s:I=app(I,t)
        V=[];v=ZERO
        for j in range(NN-P+1):
            if j<len(Q):v=add(v,Q[j])
            V.append(add(mul(bsum,v),Rs))
        cv=0
        for j in range(len(V)):
            if j<len(E):cv+=E[j]
            rhs=V[j]
            if j:rhs=add(rhs,mul(A,V[j-1]))
            if j>=2:rhs=add(rhs,mul(B,V[j-2]))
            if j==0:rhs=add(rhs,sub(mul(bsum,R0),Rs))
            if j==1:rhs=add(rhs,mul(B,Rs))
            assert rhs==sc(bsum,cv);ct['EXACT_TRUE_cumulativeE_degreeONE_source_reads']+=1
            if j:
                obs=mul(bsum,sub(sc(l,I[P+j-1]),sc(ONE,I[P+j])))
                assert obs==add(V[j],V[j-1]);ct['EXACT_ACTUAL_lambda_source_EQUALS_TWO_term_V_reads']+=1
        for j in range(1,len(V)-1):
            assert sign(sub(mul(V[j],V[j]),mul(V[j-1],V[j+1])))>=0;ct['WHOLEcumulativeQ_LC_model_reads']+=1
        ct['EXACTphysical_model_contexts']+=1
    profiles=[(a,[3]*max(32,3*s+8)+[4]*s) for s in [1,4,8] for a in [1,7]]
    old=[(2,[2]*5+[3]*5),(3,[2]*4+[4]*6),(1,[2]*3+[7,9]),(2,[3]*2+[12])]
    for i,(a,U) in enumerate(profiles):
        for b,V in profiles+old:
            F,H=arm(a,U),arm(b,V);examine(F,H,ct,sha,True)
            cap=max(U+V+[1])
            for M in [cap+1,cap+7]:core_rel(F,H,M,ct,sha,'NEW_A6_mixed_ORIGINAL')
        b,V=old[i%len(old)];F,H=arm(a,U),arm(b,V)
        t=max(4,len(H)-len(F),15+7*i);new=[1]+window(F,t)
        examine(new,H,ct,sha,False);core_rel(new,H,max(t,max(V))+1,ct,sha,'NEW_A6_one_heavier_append_ORIGINAL')
    out=dict(status='EXACT_QA_PASS_ACTUAL_THREE_FOUR_SURPLUS_COMPLETE_C_FULL_A2_AND_ORIGINAL_FAMILY',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      scope='ALLalpha>=1,r>=32,r>=3s+8 ACTUALcompleteC+ENTIREordinarytailfromr+s2 analyticallyprovedbyTRUEcumulativeQcutwith[2]futurefactor/degreeONEremainder/physicalj0. A6deletionclosed+kappa5givesFULLA2/ORIGINALcoreBOTHrelativesANYstrictpeak+ONEheavierappend. Generaloriginal/C/A2/ALLmixedoutsideconeOPEN. TestsQAonly.')
    (ROOT/'audit_mixed_three_four_surplus_actual.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
