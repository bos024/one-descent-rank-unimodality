"""Independent complete 74-host entrance, positive suffix boxes, crossing joins and sharp tails."""
from pathlib import Path
from collections import Counter
from itertools import accumulate
from random import Random
import sys,re,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
from verify_stationary_ternary_reference_C import reference_closed
def reports(name,c):
    src=(ROOT/(name+'.lean')).read_text(encoding='utf8');log=(ROOT/(name+'.log')).read_text(encoding='utf8')
    assert not any(v in log for v in ['warning:','error:','sorryAx','ofReduceBool','failed']) and 'native_decide' not in src
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==c;out={}
    for n,raw in rows:
        a=[v.strip() for v in raw.split(',') if v.strip()];assert set(a)<={'propext','Classical.choice','Quot.sound'};out[n]=a
    return out
def all_C(F,D,L,ct):
    G=list(accumulate(F));best=1
    for N in range(4,L+1):
        k=N-3
        if G[k]*G[best-1]<G[best]*G[k-1]:best=k
        assert G[best]*D[N-1]>=G[best-1]*D[N]
        ct['independent_ALL_actual_all_shift_prefix_payments']+=1;ct['independent_ALL_actual_logical_shift_reads']+=N-3
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();data=json.loads((ROOT/'all_binary_ternary_ordinary_base_data.json').read_text())
    keys={(u,alpha) for u in range(1,10) for alpha in range(1,6+u//2+1)};made={(v['u'],v['alpha']):v for v in data['contexts']}
    assert set(made)==keys and len(keys)==74;values=set()
    for u,alpha in sorted(keys):
        F=suffix_boxes(alpha,[2]*u+[3]*6)[:alpha+2*u+18+2];D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];L=D.index(max(D));row=made[u,alpha]
        assert F==row['F'] and D==row['D'] and L==row['mode'] and L<=(3*u+24)//2
        centres=list(range(9,L));ms=[F[n]**2-F[n-1]*F[n+1] for n in centres]
        assert centres==row['ordinary_centres'] and ms==row['ordinary_minors'] and all(v>=0 for v in ms)
        values.update(ms);ct['COMPLETE_independent_fixed_six_smallu_hosts']+=1;ct['COMPLETE_independent_ordinary_PRE_Dmode_minors']+=len(ms)
        sha.update(str((u,alpha,F,D,L,ms)).encode())
    assert sorted(values)==data['unique_margins'] and len(values)==296
    src=(ROOT/'AllBinaryTernaryOrdinaryBase.lean').read_text(encoding='utf8');rows=re.findall(r'^def part\d+ : List ℤ := \[([^]]*)\]$',src,re.M)
    assert len(rows)==2 and [int(v.strip()) for row in rows for v in row.split(',')]==sorted(values)
    for u in range(1,10):
        alpha=6+u//2;B=(3*u+24)//2
        F=suffix_boxes(alpha,[2]*u+[3]*6);G=suffix_boxes(alpha+73,[2]*u+[3]*6)
        assert F[:B+1]==G[:B+1];ct['independent_exact_SMALLu_largepadding_prefix_controls']+=1
    refcache={}
    for u in list(range(10,61))+[80,100,150,250]:
        r=u//2+1;W=3*r
        if r not in refcache:refcache[r]=reference_closed(r,W)
        R=refcache[r]
        for alpha in [1,2,u+r]:
            F=suffix_boxes(alpha,[2]*u+[3]*r);assert F[:W]==R[:W]
            for n in range(r+3,W-1):assert F[n]**2>=F[n-1]*F[n+1];ct['independent_PROTECTED_early_ordinary_seed_minors']+=1
            for n in range(W-1,len(F)-1):assert F[n]**2>=F[n-1]*F[n+1];ct['independent_UNIVERSAL_Wminus1_ordinary_seed_minors']+=1
            ct['independent_first_degree_crossing_JOIN_hosts']+=1;sha.update(str((u,r,alpha,F[:W+1])).encode())
    rng=Random(2026110168)
    cases=[(u,r,a) for r in range(0,19) for u in range(0,2*r+5) for a in [1,2,u+r+4]]
    cases +=[(rng.randint(0,160),rng.randint(0,120),rng.randint(1,250)) for _ in range(400)]
    fib=[0,1]
    for _ in range(500):fib.append(fib[-1]+fib[-2])
    for u,r,alpha in cases:
        F=suffix_boxes(alpha,[2]*u+[3]*r);D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];L=D.index(max(D));all_C(F,D,L,ct)
        if r>=6 and u>=1:
            if u<=2*r:
                for n in range(r+3,len(F)-1):assert F[n]**2>=F[n-1]*F[n+1];ct['independent_ENTIRE_ordinary_LC_classification_minors']+=1
            else:
                n=3*r+1;triple=[2**r*fib[j] for j in [2*r+1,2*r+2,2*r+3]]
                assert F[n-1:n+2]==triple and F[n]**2-F[n-1]*F[n+1]==-4**r
                ct['independent_EXACT_negative_four_power_actual_controls']+=1
        ct['independent_ALL_count_actual_suffix_box_hosts']+=1;sha.update(str((u,r,alpha,F,D,L)).encode())
    qa=json.loads((ROOT/'audit_all_binary_ternary_complete_C.json').read_text());assert qa['status']=='EXACT_QA_PASS_ALL_BINARY_TERNARY_ACTUAL_COMPLETE_C_AND_SHARP_ORDINARY_CLASSIFICATION_UNDER_PROOF_AUDIT'
    local=['all_binary_ternary_complete_C_proof.tex','AllBinaryTernaryCompleteC.lean','AllBinaryTernaryCompleteC.log',
      'AllBinaryTernaryOrdinaryBase.lean','AllBinaryTernaryOrdinaryBase.log','build_all_binary_ternary_ordinary_base.py',
      'all_binary_ternary_ordinary_base_data.json','audit_all_binary_ternary_complete_C.py','audit_all_binary_ternary_complete_C.json',
      'verify_all_binary_ternary_complete_C.py']
    deps=['stationary_ternary_reference_C_verification.json','stationary_ternary_reference_and_binary_dense_C_proof.tex',
      'sharp_previous_ordinary_LC_verification.json','sharp_previous_ordinary_LC_proof.tex',
      'universal_late_C_first_crossing_verification.json','surplus_ordinary_tail_LC_guard_refinement.tex',
      'ordinary_tail_to_complete_C_verification.json','ordinary_tail_to_complete_C_proof.tex','OrdinaryTailToCompleteC.lean','OrdinaryTailToCompleteC.log',
      'pure_ternary_complete_C_verification.json','multitail_binary_prefix_finite_principle_verification.json',
      'sharpened_forward_derivative_centers.tex','prefix_tp2.tex','formal_arm_extensions.tex',
      'TernaryRichCompleteC.lean','TernaryRichCompleteC.log','verify_subdegree_CI_entrance.py','verify_stationary_ternary_reference_C.py']
    out=dict(status='PASS_ALL_BINARY_TERNARY_ACTUAL_COMPLETE_C_AND_SHARP_ORDINARY_LC_CLASSIFICATION',new_scoped_reports=9,
      kernels={'AllBinaryTernaryCompleteC':reports('AllBinaryTernaryCompleteC',8),'AllBinaryTernaryOrdinaryBase':reports('AllBinaryTernaryOrdinaryBase',1)},
      theorem='EVERYACTUALnormalized1alpha2u3r,ALLalpha>=1/u>=0/r>=0:FULLC EVERYcurrent/EVERYshift>=3. BOTHcounts/padding/ranks/shiftsUNBOUNDED. Formeru<=32richrestrictionREMOVED;ALLr2u/u>=33ordinarydiagonalCLOSEDbyWEAKERroute. No strongD-minorclaim.',
      ordinary_classification='EXACTIFFforALLr>=6/u>=1/alpha>=1:ENTIREordinaryFLCfromcentreA=r+3 IFFu<=2r. ALLdeficitu<2rbyfirstdegreecrossing+heredity;u2rbyOLDsurplusentryatW+1andNEWreferenceprefixthroughW.',
      sharp_complement='EVERYACTUAL1alpha2u3r,ALLr>=6/u>=2r+1/alpha>=1:atcentreW+1=3r+1ordinaryminorEXACT-4^r<0. Protectedtriple2^r*(Fib(2r+1),Fib(2r+2),Fib(2r+3)). WholeCommRingC_r=(2z)^r+Q2J_r andwholeevenCassiniinductionkernelchecked. ThisdoesNOTrefuteC/UI.',
      analytic_entrance='EVERYu>=10,chooseFIRSTdegreecrossingr0=floor(u/2)+1>=6,u∈{2r0-2,2r0-1}. ActualFfirstdiffersfrominfinitebinaryreferenceatu+r0+2>=W,soALLordinarycentresA..W-2protected. NEWreferenceLCpays;OLDuniversalACTUALordinaryLCfromW-1(u>=5,h2r0>u)paysALLlatercentres. EXACTjoinwithNOgapandALLalpha;NOunboundeddiagonalpremise.',
      hereditary='UNIFORMALLu>=1/r>=6/alpha:ordinaryFLCtailfromr+3HEREDITARYappend3. Binaryseedheadlossesa>=1,b>=2,c>=5 KEPTWITHfinitepadding. Newfirst3lossesa,ar+b,ar(r+1)/2+br+c. BOTHleftminorspaidfornewr>=7byB-4a-1>=0/C-4B-1>=0 andactualnextF>=0. RemainingALLcentresbyLCpositive3windowofoldtail. No modecrossing/infinitephaseomission.',
      entrance='COMPLETE74hosts:u1..9,r6,ALLalpha1..6+floor(u/2),ALLordinarycentres9<=n<FIRSTDmode. 753INTEGERminors/296uniquemargins/2LeanchunksONEaggregate. ALLlargerpaddingEXACTprefixrepresentedthroughB=floor((3u+24)/2);ordinaryLCafterFIRSTDmodeOLDautomatic. SoleNEWfinitepremise;NOTparameterQA.',
      formal_scope='EIGHTnewcleanstandardaxiomgenericreports+ONEaggregateCOMPLETEfiniteordinaryentrance. IncludesFULLtwo-parameterfirstdegreecrossingseed+unboundedrinduction,WHOLEpolynomialidentityandWHOLEevenCassiniinduction. Actualcoefficient/source/old-newtailjoin/CassemblyWRITTEN,notendtoendLeancompositions. OLDuniversalsharpW-1/surplus/automaticpostDmode/newreferenceC/ordinary-to-CresourcesREUSED/NOTrecounted.',
      remaining='ORIGINALgeneralone-descentUI/generalCwitharbitrarycapacities/fullA2remainOPEN. ALLactualbinary/ternaryarmsC NOWPROVED. TheoldstrongD-minordiagonalu>=33notneeded/notasserted. Highercapacitymixedtailsandrelevantoriginalincoming/mixedsourcebranchesremain.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',all_binary_ternary_C='PROVED',counts=dict(ct),QA=qa['counts'],independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      local_files=local,dependency_files=deps,sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'all_binary_ternary_complete_C_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)
if __name__=='__main__':main()
