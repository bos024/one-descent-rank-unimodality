"""Independent A5 positive boxes, original greedy ideals, and exact sharp source counter."""
from pathlib import Path
from collections import Counter
from random import Random
import json,hashlib,time
from verify_binary_ternary_A2_original_family import SOURCE,boxes,conv,at,UI,greedy_ideal,core,check
ROOT=Path(__file__).resolve().parent
def main():
    st=time.monotonic();rng=Random(2026110187);ct=Counter();sha=hashlib.sha256()
    def profile(k,small=False):
        a=rng.randint(1,6 if small else 120);u=rng.randint(0,3 if small else 35)
        if k==0:U=[2]*u+[3]*rng.randint(0,4 if small else 35)
        elif k==1:U=[2]*u+sorted(rng.randint(3,9 if small else 120) for _ in range(rng.randint(0,2)))
        else:
            r=rng.randint(1,3 if small else 25);U=[2]*u+[3]*r+[6*r+rng.randint(0,5 if small else 150)]
        return a,U
    for case in range(630):
        a,U=profile(case%3);b,V=profile(case//3%3);A,B=boxes(a,U),boxes(b,V)
        check(A,B,ct,sha,bool(U and V))
        for F,W in [(A,U),(B,V)]:
            if W:
                k=next(n for n in range(1,7) if at(F,n)<2**(n-1));assert 3<=k<=5
                ct['independent_A5_kappa_bound_controls']+=1
        maximum=max([1]+U+V);H,L,R=core(A,B,maximum+1)
        ct['independent_A5_ORIGINAL_cores']+=1;ct['independent_A5_BOTH_relatives']+=2
        sha.update(str((a,U,b,V,H,L,R)).encode())
        if case%3==0:
            t=max(max(U+[2]),len(B)-len(A))+rng.randint(0,150)
            X=[1]+[sum(at(A,n-i) for i in range(t)) for n in range(len(A)+t-1)]
            check(X,B,ct,sha,False);core(X,B,max(t,maximum)+1)
            ct['independent_A5_arbitrary_heavier_append_originals']+=1
    for case in range(126):
        a,U=profile(case%3,True);b,V=profile(case//3%3,True)
        if case%2:
            t=max(max(U+[2]),b+sum(V)-a-sum(U))+rng.randint(0,10);U=U+[t]
        M=max([1]+U+V)+rng.randint(1,5);H,L,R=core(boxes(a,U),boxes(b,V),M)
        word=[1]*a+U+[M]+list(reversed([1]*b+V));G=greedy_ideal(word)
        assert G==H and UI(G);ct['independent_A5_GREEDY_original_ideals']+=1
        ct['independent_A5_GREEDY_original_rank_counts']+=len(G)
        sha.update(str((word,G,L,R)).encode())
    # Independently count each single arm by greedy embedding, then convolve.
    A=greedy_ideal([1,2]);B=greedy_ideal([1,5,5,5,5]);P=conv(A,B);p=P[::-1]
    E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
    assert P[3:7]==[9,17,34,65] and E[19:22]==[3,0,1]
    nu=max(i for i,x in enumerate(p) if x==max(p));assert nu==10<20
    assert not UI([max(0,e) for e in E])
    assert UI([2**n*max(0,p[n]-at(p,n-1)) for n in range(len(p))])
    # Both arms satisfy actual all-shift C; universal reason is OLD weight<=32.
    for F in [A,B]:
        d=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];G=[];v=0
        for x in F:v+=x;G.append(v)
        for n in range(4,len(F)):
            for k in range(1,n-2):
                assert G[k]*d[n-1]>=G[k-1]*d[n];ct['independent_sharp_counter_actual_C_payments']+=1
    qa=json.loads((ROOT/'audit_certified_kappa_five_original_family.json').read_text())
    assert qa['status']=='EXACT_QA_PASS_CERTIFIED_KAPPA_FIVE_ORIGINAL_FAMILY_AND_SHARP_SOURCE_BOUND'
    local=['certified_kappa_five_original_family_refinement.tex','audit_certified_kappa_five_original_family.py',
      'audit_certified_kappa_five_original_family.json','verify_certified_kappa_five_original_family.py']
    deps=['binary_ternary_A2_original_family_verification.json','binary_ternary_A2_original_family_proof.tex',
      'BinaryTernaryA2SourceCone.lean','BinaryTernaryA2SourceCone.log','SignedWindowTail.lean','SignedWindowTail.log',
      'audit_binary_ternary_A2_original_family.py','verify_binary_ternary_A2_original_family.py',
      'source_birth_gap_nonrecovery.tex','SourceBirthGapNonrecovery.lean','SourceBirthGapNonrecovery.log',
      'audit_source_birth_gap_complement.json','verify_source_birth_gap_complement.json',
      'two_nonbinary_complete_C_verification.json','two_nonbinary_complete_C_proof.tex',
      'relative_golden_head_dominant_C_verification.json','relative_golden_head_dominant_C_proof.tex',
      'all_binary_ternary_complete_C_verification.json','multitail_binary_prefix_finite_principle_verification.json']
    out=dict(status='PASS_SHARP_KAPPA_FIVE_CERTIFIED_CLASS_FULL_A2_AND_ORIGINAL_COEFFICIENT_FAMILY',new_scoped_reports=0,
      theorem='PROVED ANYfinal-deletion-closedactualarmclassEVERYmemberFULLC/kappa<=5=>FULLpairA2/ENTIREsignedsourcepositiveUIinitialinterval/ORIGINALCOREandBOTHrelativesatALLstrictpeaks;ONEarbitraryheavierappendalsoFULLA2andORIGINAL. NOnewformalreportscounted;oldkernelsreused.',
      explicit_class='A5=ALLB3 ORat-most-TWO-arbitrary-nonbinary-partswithALLbinarycounts ORB3followedbyONEdominantT>=6r,r>=1. ALLpadding/capacities/countsunbounded. CbyNEWB3/OLDtwoNONBINARY/OLDuniformdominantappend. kappa<=5 anddeletionclosed. A4issubsumed.',
      mixed_extension='Onlykappa5mixednew:ownerh>=2=>OLDsharp-gap5theorem,oppositeh>=3automatically. Ownerh1exactq=[alpha1][s]+z^a,positiveD=initialONESintervalhasNOincreasingedge. r=-1birthata-3>=0,includingRANKZEROwhenowner1,2. Noextraunprovedsmallcountpremise.',
      sharpness='ActualX1,2/Y1,5^4 BOTHcompleteC(OLDweight<=32),kappa3/6,forwardP3..6=(9,17,34,65),ENTIRErawE19..21=(3,0,1),LASTp mode10. Wholepositive-sourceUI/initialsupportFALSEatboundSIX. GeneralA2/originalNOTrefuted;thisactualpairfullA2PASS. FirstmissingFIVEsharpONLYforuniversalraw-source-coneconclusion.',
      formal_scope='ZEROnewreports. ReusesTENBinaryTernaryA2SourceCone/sevenSignedWindowTail/eightSourceBirthGapNonrecovery scopedkernelreportsandOLDindependentlyCOMPLETEgap5finitecomplement. Exactonepartformula/newclassassembly/sharpcounterWRITTENandindependentlycomputed. NewfinitechecksQAONLY,NOTnewuniversalpremise;NOTendtoendLeancompositiontheorem.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',counts=dict(ct),primary_QA=qa['counts'],
      independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,local_files=local,dependency_files=deps,
      sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'certified_kappa_five_original_family_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)
if __name__=='__main__':main()
