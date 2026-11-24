"""Independent rational bridges and actual conditional checks; no new finite premise."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
from itertools import accumulate
from random import Random
from collections import Counter
import sys,re,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
from verify_renewal_root_primitive_cut import ReciprocalRing
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256()
    for N in range(18,46):
        for offset in [0,3,7]:
            for q in [Q(2,3),Q(1),Q(3,2)]:
                f=[Q(comb(N,offset+j))*q**j for j in range(N-offset+1)];l=f[1]/f[0]
                if l<=1:continue
                g=[f[0]/(2*(l-1))]
                for v in f:g.append(g[-1]+v)
                for K in range(len(f)-2):
                    if f[K+1]<=f[K]:continue
                    mu=(f[K+2]-f[K+1])/(f[K+1]-f[K]);assert mu<=l
                    for n in range(K+2):assert mu*g[n]<=g[n+1];ct['exact_rational_complete_bridge_reads']+=1
                    ct['exact_rational_complete_bridge_contexts']+=1
                    sha.update(str((N,offset,q,K,mu,g[K+2])).encode())
    ring=ReciprocalRing(3);rng=Random(2026110128)
    cases=[(u,r,a) for u in range(1,10) for r in range(0,15) for a in [1,2,5,u+r+2]]
    cases +=[(rng.randint(1,90),rng.randint(0,140),rng.randint(1,180)) for _ in range(500)]
    for u,r,alpha in cases:
        F=suffix_boxes(alpha,[2]*u+[3]*r);D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];L=D.index(max(D));G=list(accumulate(F));A=r+3
        assert ring.sign((-F[A],F[A-1],0))>0;ct['independent_ALLcount_FIRSTsource_spectral_entries']+=1
        for n in range(L,len(F)-1):
            assert F[n]**2>=F[n-1]*F[n+1];ct['independent_automatic_ordinary_LC_after_FIRSTDmode']+=1
        condition=all(F[n]**2>=F[n-1]*F[n+1] for n in range(A,L))
        if condition:
            best=1
            for N in range(4,L+1):
                k=N-3
                if G[k]*G[best-1]<G[best]*G[k-1]:best=k
                assert G[best]*D[N-1]>=G[best-1]*D[N]
                ct['independent_ACTUAL_conditional_all_shift_payments']+=1;ct['independent_ACTUAL_logical_shift_reads']+=N-3
            ct['actual_hosts_SATISFYING_ordinary_LC_hypothesis']+=1
        else:ct['actual_hosts_EXCLUDED_by_ordinary_LC_hypothesis']+=1
        sha.update(str((u,r,alpha,F,D,L,condition)).encode())
    F=suffix_boxes(1,[2]*3+[3]);D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
    assert F[3:6]==[4,6,10] and D.index(max(D))==5 and F[4]**2-F[3]*F[5]==-4
    ct['independent_actual_negative_hypothesis_controls']=1
    src=(ROOT/'OrdinaryTailToCompleteC.lean').read_text(encoding='utf8');log=(ROOT/'OrdinaryTailToCompleteC.log').read_text(encoding='utf8')
    assert not any(x in log for x in ['warning:','error:','sorryAx','ofReduceBool','failed']) and 'native_decide' not in src
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==5;kernels={}
    for name,raw in rows:
        a=[x.strip() for x in raw.split(',') if x.strip()];assert set(a)<={'propext','Classical.choice','Quot.sound'};kernels[name]=a
    qa=json.loads((ROOT/'probe_rich_ternary_ordinary_tail.json').read_text());assert qa['status']=='DIAGNOSTIC_ONLY_RICH_TERNARY_ORDINARY_LC_ROUTE' and not qa['counterexamples']
    local=['ordinary_tail_to_complete_C_proof.tex','OrdinaryTailToCompleteC.lean','OrdinaryTailToCompleteC.log',
      'verify_ordinary_tail_to_complete_C.py','probe_rich_ternary_ordinary_tail.py','probe_rich_ternary_ordinary_tail.json']
    deps=['pure_ternary_complete_C_verification.json','PureTernaryCompleteC.lean','PureTernaryCompleteC.log',
      'first_missing_renewal_envelope.tex','finite_initial_ones_relative_derivative.tex',
      'sharpened_forward_derivative_centers.tex','prefix_tp2.tex','formal_arm_extensions.tex',
      'TernaryRichCompleteC.lean','TernaryRichCompleteC.log','ternary_rich_complete_C_verification.json',
      'ternary_forward_inverse_verification.json','verify_renewal_root_primitive_cut.py','verify_subdegree_CI_entrance.py']
    out=dict(status='PASS_CONDITIONAL_ORDINARY_TAIL_TO_COMPLETE_C_AND_UNBOUNDED_THREE_HEREDITY',new_scoped_reports=5,kernels=kernels,
      theorem='ALLACTUAL1alpha2u3r,u>=1/r>=0/alpha>=1:IFordinaryFLCatEVERYcentreA=r+3<=n<FIRSTDmodeTHENFULLC ALLranks/shifts. FIRSTactualordinarysourceentryF_A<lambda3*FprevPROVEDunconditionallybyfirstintegerloss+registeredH3residualnorm. ConditionalLCpremiseNOTproveduniversally.',
      automatic_tail='EXTRACTIONfromOLDactualDUIandreverseordinaryrisingLC:actualFautomaticallyLCatEVERYcentre>=FIRSTDmode. ThusonlystrictpreDmodeordinaryLCneedsproof;thisisWEAKERthanstrongDminororDLC.',
      heredity='ALLfixedu>=4/r>=6/alpha:ordinaryFLCfromr+3ENTIREtailishereditaryunderappend3. TWOnewordinaryentrancespaidbyOLDscalarstrongminorkernelswithEXACTlosses1,r+2,(r²+5r+10)/2;generictribonacciordinaryminorboundfrombases2,-3,1. EVERYlatercentreLCbypositive3windowoftailtruncatedatoldr+2. OldkernelsREUSED/NOTrecounted.',
      remaining_diagonal='SUFFICIENTforALLu>=4/r>=2ucompleteC:proveONLYordinaryFLCatcriticalr=2u,ALLu>=33,ALL1<=alpha<=2u+floor(u/2),centresr+3<=n<FIRSTDmode. Largerpaddingexactprefixrepresentedusingoldmodebound. QUANTIFIERuUNBOUNDED;NOTcompletedfinitecheck. Noactualrichu>=33enlargementasserted.',
      positive_companion='ExactordinarybinaryprependingF_(u+1,r)=S2F_(u,r)+1+z³B3r. AllpositivebutLCadditionisNOTautomatic;fullmixedminorsstillneeded. Frozenmacrosourceidentityretained.',
      formal_scope='FIVEnewcleanstandardaxiomreports:2scalarsteps,WHOLEbackwardordinaryratioinduction,WHOLEboundedordinary-to-Gbridge,firstintegerlossentry. Actualreferenceidentification/automaticpost-DmodeLC/append3heredity/paddingdiagonalreductionWRITTENusingOLDgenericresources. No newFINITEentrancepremise. RichordinaryLCnonfailuresONLYdiagnostic.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',counts=dict(ct),rich_diagnostic=qa,
      independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,local_files=local,dependency_files=deps,
      sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'ordinary_tail_to_complete_C_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)
if __name__=='__main__':main()
