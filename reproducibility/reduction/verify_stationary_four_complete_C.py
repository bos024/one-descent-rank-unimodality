"""Independent complete entrances, closed quartinomial references and actual suffix boxes."""
from pathlib import Path
from collections import Counter
from itertools import accumulate
from math import comb
from random import Random
import sys,json,time,re,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
from verify_ternary_forward_inverse import qa,qm,qs,sub
from verify_binary_ternary_A2_original_family import greedy_ideal,core,UI
from verify_universal_renewal_rounding import closed_G
def sc(v,k):return tuple(k*x for x in v)
def interval_power(r,n):
    if r==0:return int(n==0)
    if n<0 or n>3*r:return 0
    return sum((-1)**j*comb(r,j)*comb(n-4*j+r-1,r-1) for j in range(min(r,n//4)+1))
def reference_closed(r,N):
    # Positive affine numerator, then a binary renewal filter; no append of reference F.
    C=[int(n==0)+sum(interval_power(j,n-j-3)+interval_power(j,n-j-4) for j in range(r)) for n in range(N+1)]
    R=[]
    for n,c in enumerate(C):R.append(c+(R[-1] if n else 0)+(R[-2] if n>1 else 0))
    return R,C
def reports(name,count):
    s=(ROOT/(name+'.lean')).read_text(encoding='utf8');log=(ROOT/(name+'.log')).read_text(encoding='utf8')
    assert not any(x in log for x in ['warning:','error:','sorryAx','ofReduceBool','failed']) and 'native_decide' not in s
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==count
    out={}
    for n,raw in rows:
        ax=[v.strip() for v in raw.split(',') if v.strip()];assert set(ax)<={'propext','Classical.choice','Quot.sound'};out[n]=ax
    return out
def allC(F,ct):
    D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];G=list(accumulate(F))
    # A running minimum retained with a different update ordering.
    low=1
    for k in range(1,len(F)-3):
        N=k+3
        if G[k]*G[low-1]<=G[low]*G[k-1]:low=k
        assert D[N]*G[low-1]<=D[N-1]*G[low]
        ct['independent_actual_ALL_current_shift_payments']+=1;ct['independent_actual_logical_shifts']+=k
    return D
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();data=json.loads((ROOT/'stationary_four_complete_C_base_data.json').read_text())
    expected={(u,a) for u in range(21) for a in range(1,(u+24)//2+1)}
    made={(v['u'],v['alpha']):v for v in data['contexts']};assert len(expected)==352 and set(made)==expected
    vals=set();mscount=0
    for u,alpha in sorted(expected):
        row=made[u,alpha];F=suffix_boxes(alpha,[2]*u+[4]*8)[:alpha+2*u+34]
        D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];L=D.index(max(D));A=10 if u==0 else 11
        centres=list(range(A,L));ms=[F[n]**2-F[n-1]*F[n+1] for n in centres]
        assert F==row['F'] and D==row['D'] and L==row['L'] and L<=(3*u+40)//2
        assert centres==row['centres'] and ms==row['minors'] and all(m>=0 for m in ms)
        vals.update(ms);mscount+=len(ms);ct['COMPLETE_independent_fixed_eight_actual_hosts']+=1
        sha.update(str((u,alpha,F,D,L,ms)).encode())
    assert mscount==8554 and sorted(vals)==data['unique_margins'] and len(vals)==2815
    ct['COMPLETE_independent_actual_ordinary_PRE_Dmode_minors']=mscount
    src=(ROOT/'StationaryFourOrdinaryBase.lean').read_text(encoding='utf8')
    chunks=re.findall(r'^def part\d+ : List ℤ := \[([^]]*)\]$',src,re.M)
    assert len(chunks)==15 and [int(v.strip()) for c in chunks for v in c.split(',')]==sorted(vals)
    h=[closed_G(4,n)-closed_G(4,n-1) for n in range(18)]
    K=[(h[n]-(h[n-1] if n else 0),-(h[n-1] if n else 0)) for n in range(len(h))]
    R,C=reference_closed(8,32);H=[(R[n]-(R[n-1] if n else 0),-(R[n-1] if n else 0)) for n in range(len(R))]
    assert h==data['h'] and list(map(list,K))==data['K'] and C==data['C8'] and list(map(list,H))==data['H8']
    tags=set();expected_tags=set()
    for n in range(2,9):expected_tags.update(['hminor_minus_'+str(n),'hminor_plus_'+str(n)])
    for n in range(7,14):expected_tags.update(['Kminor_minus_'+str(n),'Kminor_plus_'+str(n)])
    for name,indices in [('K_lower_growth',range(5,9)),('K_upper_growth',range(6,10)),('K_positive',range(2,6)),('h_lower_growth',range(1,5)),('h_upper_growth',range(1,5)),('H8_positive',range(10,33)),('H8_LC',range(11,32))]:
        expected_tags.update(name+'_'+str(n) for n in indices)
    assert len(expected_tags)==92 and len(data['field_rows'])==92
    fieldsrc=(ROOT/'StationaryFourFieldBase.lean').read_text(encoding='utf8')
    for row in data['field_rows']:
        tag=row['tag'];n=int(tag.rsplit('_',1)[1]);tags.add(tag)
        if tag.startswith('hminor'):
            m=h[n]**2-h[n-1]*h[n+1];v=(h[n-1]+(m if 'plus' in tag else -m),0)
        elif tag.startswith('Kminor'):
            m=sub(qm(K[n],K[n]),qm(K[n-1],K[n+1]));v=qa(K[n-1],m) if 'plus' in tag else sub(K[n-1],m)
        elif tag.startswith('K_lower'):v=sub(sc(K[n+1],5),sc(K[n],9))
        elif tag.startswith('K_upper'):v=sub(sc(K[n],2),K[n+1])
        elif tag.startswith('K_positive'):v=K[n]
        elif tag.startswith('h_lower'):v=(5*h[n+1]-9*h[n],0)
        elif tag.startswith('h_upper'):v=(2*h[n-1]-h[n],0)
        elif tag.startswith('H8_positive'):v=H[n]
        else:v=sub(qm(H[n],H[n]),qm(H[n-1],H[n+1]))
        assert list(v)==row['value'] and (qs(v)>0 if row['strict'] else qs(v)>=0)
        prop=f'0{ "<" if row["strict"] else "≤" }(({v[0]}:ℝ)+({v[1]}:ℝ)*q)';assert prop in fieldsrc
        ct['COMPLETE_independent_field_majorant_and_reference_scalars']+=1
    assert tags==expected_tags
    for u in range(21):
        alpha=(u+24)//2;B=(3*u+40)//2
        assert suffix_boxes(alpha,[2]*u+[4]*8)[:B+1]==suffix_boxes(alpha+100,[2]*u+[4]*8)[:B+1]
        ct['independent_exact_large_padding_prefix_clamps']+=1
    cache={}
    for u in list(range(21,91))+[100,150,200]:
        r=u//3+1;W=4*r
        if r not in cache:cache[r]=reference_closed(r,W+2)[0]
        R=cache[r]
        for alpha in [1,2,u+r]:
            F=suffix_boxes(alpha,[2]*u+[4]*r);assert F[:W-1]==R[:W-1]
            for n in range(r+3,len(F)-1):assert F[n]**2>=F[n-1]*F[n+1];ct['independent_ENTIRE_first_degree_crossing_ordinary_seed_minors']+=1
            ct['independent_all_large_binary_analytic_seed_QA_hosts']+=1
    rng=Random(2026110195)
    cases=[(u,r,a) for r in range(0,20) for u in range(0,3*r+5) for a in [1,2,u+r+3]]
    cases +=[(rng.randint(0,120),rng.randint(0,70),rng.randint(1,150)) for _ in range(180)]
    for u,r,alpha in cases:
        F=suffix_boxes(alpha,[2]*u+[4]*r);allC(F,ct)
        if r>=8:
            A=r+2 if u==0 else r+3
            if u<=3*r:
                for n in range(A,len(F)-1):assert F[n]**2>=F[n-1]*F[n+1];ct['independent_ENTIRE_actual_ordinary_LC_minors']+=1
            else:
                n=4*r+1;assert F[n]**2-F[n-1]*F[n+1]==-5**r;ct['independent_EXACT_negative_five_power_controls']+=1
        ct['independent_all_binary_four_count_suffix_box_hosts']+=1;sha.update(str((u,r,alpha,F)).encode())
    for case in range(72):
        a,b=rng.randint(1,7),rng.randint(1,7);U=[2]*rng.randint(0,5)+[4]*rng.randint(0,5)
        V=[2]*rng.randint(0,5)+([3]*rng.randint(0,5) if case%2 else sorted(rng.randint(3,10) for _ in range(2)))
        M=max([1]+U+V)+rng.randint(1,5);A=suffix_boxes(a,U)[:a+sum(U)+1];B=suffix_boxes(b,V)[:b+sum(V)+1]
        H,L,R=core(A,B,M);host=[1]*a+U+[M]+list(reversed([1]*b+V));actual=greedy_ideal(host)
        assert H==actual and UI(actual);ct['independent_TRUE_GREEDY_enlarged_ORIGINAL_ideals']+=1
        ct['independent_TRUE_GREEDY_ORIGINAL_rank_counts']+=len(actual)
    primary=json.loads((ROOT/'audit_stationary_four_complete_C.json').read_text());assert primary['status']=='EXACT_QA_PASS_ALL_BINARY_FOUR_COMPLETE_C_SHARP_ORDINARY_TAIL_AND_ORIGINAL_FAMILY_UNDER_PROOF_AUDIT'
    local=['stationary_four_complete_C_proof.tex','StationaryFourCompleteC.lean','StationaryFourCompleteC.log',
      'StationaryFourFieldBase.lean','StationaryFourFieldBase.log','StationaryFourOrdinaryBase.lean','StationaryFourOrdinaryBase.log',
      'build_stationary_four_complete_C_bases.py','stationary_four_complete_C_base_data.json',
      'audit_stationary_four_complete_C.py','audit_stationary_four_complete_C.json','verify_stationary_four_complete_C.py']
    deps=['universal_renewal_rounding_verification.json','universal_renewal_rounding_and_ordinary_C_bridge_proof.tex',
      'verify_universal_renewal_rounding.py','universal_physical_boundary_C_verification.json',
      'sharp_previous_ordinary_LC_verification.json','sharp_previous_ordinary_LC_proof.tex',
      'universal_late_C_first_crossing_verification.json','surplus_ordinary_tail_LC_guard_refinement.tex',
      'relative_golden_head_dominant_C_verification.json','relative_golden_head_dominant_C_proof.tex',
      'arbitrary_Fibonacci_tail_late_C_verification.json','multitail_binary_prefix_finite_principle_verification.json',
      'ordinary_tail_to_complete_C_proof.tex','ordinary_tail_to_complete_C_verification.json',
      'sharpened_forward_derivative_centers.tex','prefix_tp2.tex','formal_arm_extensions.tex',
      'renewal_root_primitive_cut_verification.json','renewal_root_positive_primitive_cut_proof.tex',
      'certified_kappa_five_original_family_verification.json','certified_kappa_five_original_family_refinement.tex',
      'verify_subdegree_CI_entrance.py','verify_ternary_forward_inverse.py','verify_binary_ternary_A2_original_family.py',
      'audit_binary_ternary_A2_original_family.py']
    out=dict(status='PASS_ALL_BINARY_FOUR_ACTUAL_COMPLETE_C_SHARP_ORDINARY_CLASSIFICATION_AND_ORIGINAL_FAMILY',new_scoped_reports=13,
      kernels={'StationaryFourCompleteC':reports('StationaryFourCompleteC',11),'StationaryFourFieldBase':reports('StationaryFourFieldBase',1),'StationaryFourOrdinaryBase':reports('StationaryFourOrdinaryBase',1)},
      actual_C='PROVED EVERYactual1alpha2u4r,ALLalpha>=1/u,r>=0 FULLC EVERYcurrent/EVERYshift. BOTHcounts/padding/ranksUNBOUNDED. NOunboundeddiagonalpremise.',
      reference='PROVED R_r=B4r+S4rH2 FULLC ALLr;forALLr>=8 HphiLCcentresr3..W-1,ordinaryRLCr3..W,firstlateordinaryminorW1=-5^r. ALLpositiveH2..W/WHOLEalternatingtailKEPT.',
      seven_step='EXACTquarticminorM_n7=-M_n+2M_n1-3M_n2+4M_n3-M_n5;absoluteweightedblocknorm4417475/4782969<1atgrowth9/5. WHOLEmajorantinductionfromSEVENentrances,forhcentres2..8/Kcentres7..13;growthALLranksfromFOURpositive4recurrenceseeds. NOspectral/conjugateassumption.',
      startup_corners='THREEleftminorspaidbyB-4a-1/C-4B-1/D-4C-1withACTUALsuccessorsnonnegative. Referenceheadseed1,b>=1,c>=2,d>=4,newr>=9. ActualbinaryseedALLpaddinga>=1,b>=2a,c>=4a-1,d>=8a-3,newr>=8. TerminalTWOcornersuseONLYlast4inverseCIvalues,NOTglobalquotientLC;(r2)*(3-4q)^r<=1ALLr>=4pluscompleteexactcorneridentities.',
      analytic_seed='ALLu>=21,r0=floor(u/3)+1>=8. FIRSTactual/referencebinarylossu+r0+2>=W-1;ordinaryA..W-3protectedandcentreW-2protectedORsuccessorLOWEREDimproves. OLDuniversalactualordinaryLCfromW-1(u>=5,h3r0>u)joinswithNOgap. Append4ordinaryheredityALLr>=r0. Denseu>=3r-3referenceCthroughW-1+OLDactualCfromW.',
      complete_entrance='COMPLETE352hosts:u0..20/r8/alpha1..floor((u+24)/2),8554ordinaryPRE_FIRSTDmode minors/2815uniqueintegers/15chunksONEaggregate. ALLlargerpaddingexactprefixthroughB=floor((3u+40)/2),Dmode<=B;automaticordinaryLCafterDmode. PLUSONEfieldaggregate92EXACTscalarscoversallh/Kmajorant/growthseeds+H8positive10..32/all21LCminors11..31. ALLindependentlyreconstructed.',
      sharp_classification='PROVEDALLr>=8/u>=1/alpha:ENTIREordinaryFLCfromr3 IFFu<=3r;u0LCfromr2. Boundaryu3rreferenceprotectedthroughW1andOLDsurplusordinaryentryW1. ALLu>=3r+1actualminorW1=-5^r. WHOLEC_r=(2-z)^r+Q2J_r,degreeJ<=W-2,quadraticnorm5andFibonacciCassini. NegativeordinaryminorNOTaC/UIcounter.',
      original_family='PROVEDORIGINALunamplifiedCORE/BOTHrelativesALLstrictpeaks,FULLpairA2andENTIREpositive-sourceconeforclassA5 UNIONALLbinary/fourarms,withONEarbitraryheavierappendalsoallowed. UsesPROVEDkappa5Ccriterion;NOextraformalreport. Onearmmayhavemanythrees/oppositemanyfours. WITHINonearmMIXED3and4NOTasserted.',
      formal_scope='ELEVENNEWcleanstandard-axiomGENERICreports+TWOcompleteentranceaggregates=13countedONCE. Actualreference/CI/finitehost/source/LCconvolution/old-resourceandallu/r/originalassemblyWRITTEN,NOTendtoendLeancompositions. ONLYcomplete352host/92scalarentrancesarefiniteproofpremises;parameterQAdiagnosticsonly.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',mixed_three_four_single_arm_C='OPEN',
      counts=dict(ct),primary_QA=primary['counts'],independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      local_files=local,dependency_files=deps,sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'stationary_four_complete_C_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['sha256','kernels']}),flush=True)
if __name__=='__main__':main()
