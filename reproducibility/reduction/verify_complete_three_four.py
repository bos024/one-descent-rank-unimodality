"""COMPLETE independent proof-base reconstruction plus separate true-ideal QA."""
from pathlib import Path
from collections import Counter
import sys,json,time,hashlib,re,ast
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
from verify_binary_ternary_A2_original_family import boxes,check,core,greedy_ideal,UI
from verify_mixed_three_four_proper_quotient import ci,proper_forward
from verify_universal_renewal_rounding import closed_G
from audit_renewal_root_primitive_cut import RootField

def into_lambda(v):
    # q=lambda²-lambda-1, q²=2lambda-lambda².
    x,y,z=v;return (x-y,-y+2*z,y-z)
def lower(v,N,M):
    a,b,c=v
    return a*M*M+b*(N if b>=0 else N+1)*M+c*(N*N if c>=0 else (N+1)*(N+1))
def reports(name,count):
    src=(ROOT/(name+'.lean')).read_text();log=(ROOT/(name+'.log')).read_text()
    assert not any(s in log for s in ['warning:','error:','sorryAx','ofReduceBool','failed']) and 'native_decide' not in src
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
    zero=re.findall(r"'([^']+)' does not depend on any axioms",log);assert len(rows)+len(zero)==count
    out={n:[] for n in zero}
    for n,raw in rows:
        ax=[s.strip() for s in raw.split(',') if s.strip()];assert set(ax)<={'propext','Classical.choice','Quot.sound'};out[n]=ax
    return out
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();integers=set();fields=set()
    data=json.loads((ROOT/'complete_three_four_boundary_data.json').read_text())
    oldroot=json.loads((SOURCE/'tribonacci_inverse_complete_certificate_data.json').read_text())
    N,M=data['root_lower_numerator'],data['root_denominator']
    assert (N,M)==(oldroot['root_lower_numerator'],oldroot['root_denominator'])
    assert N**3-N*N*M-N*M*M-M**3<0<(N+1)**3-(N+1)**2*M-(N+1)*M*M-M**3
    ordinary_expected={};three_expected=set();reused_expected=set()
    for r in range(1,50):
        star=max(8,(r+4)//3)
        ordinary_expected[r,star]='four_heredity_entrance'
        for s in range(1,star):
            if 3*r+4*s<=32 or(r>=32 and r>=3*s+8):reused_expected.add((r,s))
            elif r+2<=3*s:ordinary_expected[r,s]='small_four_phase'
            else:three_expected.add((r,s))
    assert len(ordinary_expected)==96 and len(three_expected)==207 and len(reused_expected)==224
    assert {tuple(v) for v in data['reused_old_C_pairs']}==reused_expected
    ordinary={(d['r'],d['s']):d for d in data['ordinary_contexts']}
    assert len(ordinary)==len(data['ordinary_contexts']) and set(ordinary)==set(ordinary_expected)
    for row in data['ordinary_contexts']:
        r,s=row['r'],row['s'];w=r+s;L=(4*r+5*s)//2;A=s+(3 if r==1 else 4);alpha0=L-w+1
        assert (row['kind'],row['L'],row['A'],row['alpha_clamp'])==(ordinary_expected[r,s],L,A,alpha0)
        local=0
        for alpha in range(1,alpha0+1):
            # Independent sum of positive suffix boxes, no chronological recurrence.
            F=suffix_boxes(alpha,[3]*r+[4]*s)[:L+1]
            for n in range(A,L):
                v=F[n]**2-F[n-1]*F[n+1];assert v>=0
                integers.add(v);local+=1;ct['independent_COMPLETEordinary_minors']+=1
            sha.update(str((r,s,alpha,F)).encode());ct['independent_COMPLETEordinary_hosts']+=1
        assert local==row['minor_count'];ct['independent_COMPLETEordinary_contexts']+=1
    assert sha.hexdigest()==data['ordinary_state_sha256']
    assert ct['independent_COMPLETEordinary_hosts']==2957 and ct['independent_COMPLETEordinary_minors']==180306
    print(json.dumps(dict(phase='ALLordinary_bases_independently_reconstructed',counts=dict(ct))),flush=True)
    three={(d['r'],d['s']):d for d in data['three_cut_contexts']}
    assert len(three)==len(data['three_cut_contexts']) and set(three)==three_expected
    f=RootField(3);b=f.q;l=f.add(f.one,f.add(b,f.mul(b,b)));a=f.sub(l,f.one);Bsum=f.add(f.one,f.add(a,b))
    h3=lambda n:closed_G(3,n)-closed_G(3,n-1)
    for (r,s),row in sorted(three.items()):
        E=ci(r,s);Q=proper_forward(f,E)
        assert E==row['E'] and [list(into_lambda(v)) for v in Q]==row['Q']
        R0=f.sub(f.one,Q[0]);R1=f.sub(f.sub(f.scale(f.one,r+s),Q[1]),f.mul(a,Q[0]));Rs=f.add(R0,R1)
        assert [list(into_lambda(v)) for v in [R0,R1]]==row['remainder']
        for n,en in enumerate(E):
            v=f.zero
            if n<len(Q):v=f.add(v,Q[n])
            if 0<=n-1<len(Q):v=f.add(v,f.mul(a,Q[n-1]))
            if 0<=n-2<len(Q):v=f.add(v,f.mul(b,Q[n-2]))
            if n==0:v=f.add(v,R0)
            if n==1:v=f.add(v,R1)
            assert v==f.scale(f.one,en);ct['independent_COMPLETEproper_division_identity_reads']+=1
        assert all(f.sign(v)>0 for v in Q)
        ms=[f.sub(f.mul(Q[n],Q[n]),f.mul(Q[n-1],Q[n+1])) for n in range(1,len(Q)-1)]
        assert all(f.sign(v)>=0 for v in ms)
        V0=f.add(f.mul(Bsum,Q[0]),Rs);V1=f.add(V0,f.mul(Bsum,Q[1]));V2=f.add(V1,f.mul(Bsum,Q[2]));seed=f.sub(f.mul(V1,V1),f.mul(V0,V2))
        assert f.sign(V0)>0 and f.sign(seed)>=0
        assert list(into_lambda(V0))==row['V0_scaled'] and list(into_lambda(seed))==row['Vseed_scaled']
        entry=(1-2**s*h3(r+2),2**s*h3(r+1),0);assert list(entry)==row['entry'] and lower(entry,N,M)>0
        for v in Q+ms+[V0,seed]:
            if v!=f.zero:fields.add(into_lambda(v))
        fields.add(entry)
        P=r+s+2;U=[3]*r+[4]*s;I=suffix_boxes(P+3,U);F=suffix_boxes(1,U)
        mI=I[P]**2-I[P-1]*I[P+1];mF=F[P]**2-F[P-1]*F[P+1]
        assert (mI,mF)==(row['infinite_padding_j0_minor'],row['alpha_one_j0_minor']) and min(mI,mF)>=0
        integers.update([mI,mF]);assert r+s>=10 and r+2>3*s
        ct['independent_COMPLETE_Q_positive_values']+=len(Q);ct['independent_COMPLETE_Q_GLOBAL_LC_minors']+=len(ms)
        ct['independent_COMPLETE_V_seeds_and_ROOTentries']+=1;ct['independent_COMPLETEtwo_physical_j0_boundaries']+=2
    assert ct['independent_COMPLETE_Q_positive_values']==14914 and ct['independent_COMPLETE_Q_GLOBAL_LC_minors']==14500
    seeds={(d['r'],d['alpha']):d for d in data['startup_seed_contexts']}
    assert len(seeds)==35 and set(seeds)=={(r,alpha) for r in range(1,6) for alpha in range(1,8)}
    for (r,alpha),row in seeds.items():
        F=boxes(alpha,[3]*r);hh=[closed_G(4,n)-closed_G(4,n-1) for n in range(8)]
        at=lambda n:F[n] if n<len(F) else 0;a0=3 if r==1 else 4
        losses=[hh[n]-at(n) for n in range(a0,a0+4)];aa,bb,cc,dd=losses
        budgets=[aa-1,bb-2*aa,cc-4*aa+1,dd-8*aa+3]
        assert row['first']==a0 and row['losses']==losses and row['budgets']==budgets
        assert min(budgets)>=0 and [at(n) for n in range(a0)]==hh[:a0]
        integers.update(budgets);ct['independent_COMPLETEstartup_seed_contexts']+=1
    assert sorted(integers)==data['integer_margins'] and len(integers)==59933
    assert sorted(fields)==[tuple(v) for v in data['field_scalars']] and len(fields)==29198
    assert all(lower(v,N,M)>0 for v in fields)
    # Check EVERY actual generated kernel payload, including its aggregate coverage.
    src=(ROOT/'CompleteThreeFourOrdinaryBase.lean').read_text()
    chunks=[ast.literal_eval(z) for z in re.findall(r'def chunk\d+ : List ℤ := (\[[^\n]+\])',src)]
    assert len(chunks)==data['integer_chunks']==333 and [v for c in chunks for v in c]==sorted(integers)
    expected=' && '.join(f'chunk{i}.all (fun z => decide (0 ≤ z))' for i in range(len(chunks)))
    assert expected in src
    src=(ROOT/'CompleteThreeFourRootBase.lean').read_text()
    chunks=[ast.literal_eval(z) for z in re.findall(r'def chunk\d+ : List \(ℤ × ℤ × ℤ\) := (\[[^\n]+\])',src)]
    assert len(chunks)==data['field_chunks']==305 and [tuple(v) for c in chunks for v in c]==sorted(fields)
    expected=' && '.join(f'chunk{i}.all (fun v => decide (0 < lowerNumerator v))' for i in range(len(chunks)))
    assert expected in src and f'let N : ℤ := {N}' in src and f'let M : ℤ := {M}' in src
    assert 'A*M*M+B*(if 0 ≤ B then N else N+1)*M+C*(if 0 ≤ C then N*N else (N+1)*(N+1))' in src
    ct['COMPLETEkernel_INTEGERpayload_values']=len(integers);ct['COMPLETEkernel_ALGEBRAICpayload_values']=len(fields)
    sha.update(str((sorted(integers),sorted(fields))).encode())
    if '--reconstruct-only' in sys.argv:
        print(json.dumps(dict(status='PASS_COMPLETE_INDEPENDENT_THREE_FOUR_BOUNDARY_RECONSTRUCTION',counts=dict(ct),sha256=sha.hexdigest(),seconds=time.monotonic()-st)),flush=True);return
    kernels=dict(CompleteThreeFour=reports('CompleteThreeFour',3),CompleteThreeFourOrdinaryBase=reports('CompleteThreeFourOrdinaryBase',1),
      CompleteThreeFourRootBase=reports('CompleteThreeFourRootBase',1))
    # Separate QA of actual complete C and original distinct-composition counts.
    for r,s in [(0,30),(1,50),(2,80),(5,35),(12,2),(20,10),(31,5),(40,17),(55,100)]:
        for alpha in [1,2,9]:
            F=boxes(alpha,[3]*r+[4]*s)+[0,0];G=[];v=0
            for x in F:v+=x;G.append(v)
            d=[max(0,F[n]-F[n-1]) if n>=2 else 0 for n in range(len(F))]
            for NN in range(4,len(F)):
                for k in range(1,NN-2):
                    assert G[k]*d[NN-1]>=G[k-1]*d[NN];ct['independent_QA_ALLcurrent_ALLshift_actual_C_reads']+=1
    old=[(1,[2]*3+[3]*4),(2,[2]*2+[4]*5),(1,[2]*2+[7,9]),(1,[3]*3+[18])]
    for case in range(36):
        r,s=[(1,20),(2,35),(4,50),(9,30),(20,5),(32,80)][case%6];alpha=1+case%2;U=[3]*r+[4]*s
        if case%4==0:beta=2;V=[3]*3+[4]*25
        else:beta,V=old[case%4]
        appended=False
        if case%8==0:
            t=max(4,beta+sum(V)-alpha-sum(U),12+case);U=U+[t];appended=True
        F,H=boxes(alpha,U),boxes(beta,V)
        if appended:assert len(F)>=len(H)
        check(F,H,ct,sha,not appended)
        peak=max(U+V+[1])+1;C,L,R=core(F,H,peak)
        host=[1]*alpha+U+[peak]+list(reversed([1]*beta+V));actual=greedy_ideal(host)
        assert actual==C and UI(actual);ct['independent_TRUE_GREEDY_A8_ORIGINAL_ideals']+=1
        ct['independent_TRUE_GREEDY_A8_ORIGINAL_rank_counts']+=len(actual);ct['independent_A8_BOTH_relative_polynomials']+=2
        if appended:ct['independent_TRUE_GREEDY_A8_heavier_append_ideals']+=1
        sha.update(str((host,actual,L,R)).encode())
    primary=json.loads((ROOT/'audit_complete_three_four.json').read_text())
    assert primary['status']=='EXACT_QA_PASS_COMPLETE_ACTUAL_THREE_FOUR_C_AND_A8_ORIGINAL_FAMILY'
    local=['complete_three_four_actual_C_original_proof.tex','CompleteThreeFour.lean','CompleteThreeFour.log',
      'CompleteThreeFourOrdinaryBase.lean','CompleteThreeFourOrdinaryBase.log','CompleteThreeFourRootBase.lean','CompleteThreeFourRootBase.log',
      'build_complete_three_four_bases.py','complete_three_four_boundary_data.json','audit_complete_three_four.py','audit_complete_three_four.json','verify_complete_three_four.py']
    deps=['three_four_all_four_counts_verification.json','three_four_all_four_counts_actual_C_original_proof.tex','ThreeFourAllFourCounts.lean','ThreeFourAllFourCounts.log',
      'mixed_three_four_surplus_actual_verification.json','mixed_three_four_surplus_actual_C_original_proof.tex','MixedThreeFourActualCut.lean','MixedThreeFourActualCut.log',
      'infinite_three_four_reference_C_verification.json','infinite_three_four_reference_complete_C_proof.tex',
      'renewal_root_primitive_cut_verification.json','renewal_root_positive_primitive_cut_proof.tex','RenewalRootPrimitiveCut.lean','RenewalRootPrimitiveCut.log',
      'StationaryFourCompleteC.lean','StationaryFourCompleteC.log','sharpened_forward_derivative_centers.tex','SharpenedForwardDerivativeCenters.lean','SharpenedForwardDerivativeCenters.log',
      'multitail_binary_prefix_finite_principle_verification.json','multitail_binary_prefix_finite_principle.tex',
      'universal_renewal_rounding_verification.json','universal_renewal_rounding_and_ordinary_C_bridge_proof.tex',
      'certified_kappa_five_original_family_verification.json','certified_kappa_five_original_family_refinement.tex',
      'TribonacciInverseClosure.lean','TribonacciInverseClosure.log','TribonacciInverseCompleteCertificate.lean','TribonacciInverseCompleteCertificate.log',
      'tribonacci_inverse_complete_certificate_data.json','verify_mixed_three_four_proper_quotient.py',
      'verify_binary_ternary_A2_original_family.py','audit_binary_ternary_A2_original_family.py','verify_subdegree_CI_entrance.py',
      'verify_universal_renewal_rounding.py','audit_renewal_root_primitive_cut.py','probe_tribonacci_quadratic_inverse.py','build_tribonacci_rich_reverse_certificate.py']
    out=dict(status='PASS_COMPLETE_ALL_COUNT_ACTUAL_THREE_FOUR_C_AND_A8_ORIGINAL_UNAMPLIFIED_COEFFICIENT_FAMILY',new_scoped_reports=5,kernels=kernels,
      actual_C='EVERYalpha>=1/r>=0/s>=0:ACTUAL1alpha3r4s FULLC ALLcurrent/ALLshift. ALLthree/fourcountsandpaddingUNBOUNDED,NOcutoff/surplusratio. Binaryprefixu>=1isSEPARATEandOPEN.',
      finite_reduction='AnalyticALLr>=50REUSED. r1..49 star=max8,floor((r+4)/3)in8..17;49FIXEDordinary4entrances+35seedlosscontexts+WHOLE4heredity=>ALLs>=star. BelowstarEXACT224oldC pairs/47ordinaryfourphase/207properQcutpredicatepairs,completepartition. NOunboundeddiagonalfinitepremise.',
      padding='SHARPfirstDmodeL=floor((4r+5s)/2),valid>=2sortednonones;autoordinaryLCfromfirstDmode. FiniteordinarycentresA..L-1onlyread<=L. alpha0=L-(r+s)+1 protectsALLprefixreads forEVERYalpha>=alpha0. EXACT2957hosts/180306ordinaryminors across96contexts,completeALLalphaclamp.',
      conditional_cut='For207smallthreephasepairs,NOquarterbox/largecountpremise:properQpositiveGLOBALordinaryLC,V0>0,Vfirstcumulativeminor>=0,physicalj0minorforINFINITEpaddingandalpha1>=0,strictROOTentry. TheseEXACTpredicates+TRUEdegreeONEsource/[2]futuremodel+NEWALLREALw>=10startupbudgets=>ENTIREordinaryactualtail/FULLC ALLalpha. alpha2onlynextreadlowered;alpha>=3j0unchanged. ALLothercomponentsandmodeguardsretained.',
      complete_certificate='59933distinctNONNEGATIVEINTEGERmargins333chunksONEAXIOMFREEaggregate;29198distinctSTRICTLYpositivequadraticFIELDscalars305chunksONEAXIOMFREEaggregateusingOLDexact50digitrationalcubicrootinterval. ENTIRE14914properQcoeffs/14500minors+Vseeds/rootentries+414physicalj0margins+35seedcontexts. Independentpositiveboxes/closedCI/qbasisFORWARDdivisionmatchesALLstates/partition/scalarsets/generatedchunks;notrandompremises.',
      original_A8='A8=A7 UNIONALL1alpha3r4s ALLr/s. Finaldeletionclosed,C,kappa<=5 =>FULLpairA2/ENTIREpositive-sourceconeforbothnonrect/ORIGINALCOREandBOTHrelativesANYstrictcentralpeak+ONEarbitrarylegalheavierappend. NOamplification. WithinONEarmBOTHthree/fourcountsCOMPLETELYUNRESTRICTED.',
      formal_scope='FIVENEWreports:THREEcleanstandardaxiomSCOPEDunboundedsourcebudget/paddingphasearithmetic/wholeNat2countreduction +TWOAXIOMFREECOMPLETEfiniteproofaggregates. Allsignedcut/cumulativeprimitive/mode/referenceC/rootinterval/4startups/kappa5originalkernelsREUSEDwithoutrecount. Actualmodel/LCconvolution/degree/root-sign/wholeoriginalassemblyWRITTEN,notendtoendLeancompositions. NEWfiniteproofpremisesEXPLICITCOMPLETE96ordinary/207Qcontexts;extraQAseparate.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',mixed_three_four_single_arm_C='PROVED_ALLr_ALLs_ALLalpha',full_mixed_binary_three_four_C='OPEN',
      next='ALL1alpha3r4s nowC/ORIGINALfamily. NEXTarbitrarybinaryprefix1alpha2u3r4s:EXTRAsourcecomponentsneedretaining;derivegenericinitial-binarysmoothingor3phaseordinarycut,notautomaticfromnewtheorem. Beyondcapacity4/generalunamplifiedoriginalstillOPEN.',
      counts=dict(ct),primary_QA=primary['counts'],independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      local_files=local,dependency_files=deps,sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'complete_three_four_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['sha256','kernels']}),flush=True)
if __name__=='__main__':main()
