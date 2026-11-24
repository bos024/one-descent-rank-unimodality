"""Independent COMPLETE owner table plus separate generic/actual/original QA."""
from pathlib import Path
from collections import Counter
from random import Random
import sys,json,re,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_binary_ternary_A2_original_family import boxes,conv,core,greedy_ideal,UI

def at(a,n):return a[n] if 0<=n<len(a) else 0
def win(E,t):return [sum(at(E,n-j) for j in range(t)) for n in range(len(E)+t-1)]
def reports(name,count):
    src=(ROOT/(name+'.lean')).read_text(encoding='utf8');log=(ROOT/(name+'.log')).read_text(encoding='utf8')
    assert 'native_decide' not in src and not any(x in log for x in ['warning:','error:','sorryAx','ofReduceBool','failed'])
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==count
    out={}
    for n,v in rows:
        a=[x.strip() for x in v.split(',') if x.strip()]
        assert set(a)<={'propext','Classical.choice','Quot.sound'};out[n]=a
    return out
def main():
    st=time.monotonic();ct=Counter();integers=set();sha=hashlib.sha256();rng=Random(730117)
    data=json.loads((ROOT/'kappa_seven_owner_certificate_data.json').read_text(encoding='utf8'))
    states={};exceptions=[]
    # Independent partition-by-DEGREE grammar, rather than by capacity bounds.
    for D in range(2,37):
        words=[[2,D]]
        for x in range(1,D):
            y=D-1-x
            if x<=y:words.append([2,x+1,y+1])
        for U in words:
            A=boxes(1,U);a=len(A)-1;q=A[::-1];s=[v-at(q,n-1) for n,v in enumerate(q)];rows=[]
            for r in range(a):
                C=s[r+1]-s[r]
                if s[r]<0 or C<=0:continue
                n=a-r-6;pay=at(A,n)+at(A,n-2);v=pay-C
                row=dict(r=r,curvature=C,birth_index=n,payment=pay,margin=v);rows.append(row)
                ct['all_positive_curvature_edges']+=1
                if v<0:
                    exceptions.append(dict(U=U,a=a,D=D,**row));ct['unpaid_exception_edges']+=1
                else:integers.add(v);ct['kernel_payment_obligations']+=1
            state=dict(U=U,D=D,weight=a,forward=A,reverse=q,ALL_curvature_rows=rows)
            assert tuple(U) not in states;states[tuple(U)]=state;ct['complete_owner_states']+=1
    assert len(states)==341 and len(exceptions)==2
    assert {tuple(x['U']) for x in data['states']}==set(states)
    for state in data['states']:
        actual=states[tuple(state['U'])];assert actual==state
        sha.update(json.dumps(actual,separators=(',',':')).encode())
    assert dict(ct)==data['counts'] and sha.hexdigest()==data['state_sha256']
    assert sorted(exceptions,key=lambda v:v['U'])==sorted(data['exceptions'],key=lambda v:v['U'])
    values=sorted(integers);assert values==data['integer_margins'] and len(values)==71
    src=(ROOT/'KappaSevenOwnerCertificate.lean').read_text(encoding='utf8')
    expr=' && '.join(f'decide ((0 : Int) ≤ {v})' for v in values)
    assert 'private theorem chunk_0 : ('+expr+') = true := by decide' in src
    assert 'theorem complete_all_owner_payments : (('+expr+')) = true := by\n  simp only [chunk_0]' in src
    finite_counts=dict(ct);finite_sha=sha.hexdigest()
    kernels={'GeneralFiniteSourcePatch':reports('GeneralFiniteSourcePatch',3),
        'KappaSevenWindowRepair':reports('KappaSevenWindowRepair',5),'KappaSevenOwnerCertificate':reports('KappaSevenOwnerCertificate',1)}
    # Separate QA: arbitrary critical block width and height; the FIRST outgoing
    # coefficient may be below its height, unlike the old three-rank lemma.
    for j in range(1800):
        L=rng.randint(2,30);mode=rng.randint(0,L)
        left=sorted(rng.randint(1,40) for _ in range(mode+1))
        right=sorted((rng.randint(1,left[-1]) for _ in range(L-mode)),reverse=True)
        c=left+right;B=rng.randint(1,L);H=min(c[1:B+1]);R=L+rng.randint(1,9)
        E=c+[rng.randint(0,H) for _ in range(R-L)]+[-rng.randint(0,30) for _ in range(5)]
        t=R-B+rng.randint(0,7);assert t>=1
        W=win(E,t);P=[max(0,x) for x in W];assert UI(P)
        pos=[n for n,x in enumerate(P) if x>0];assert pos==list(range(pos[-1]+1))
        ct['independent_arbitrary_height_width_source_patch_profiles']+=1
        if c[0]<H:ct['independent_first_outgoing_below_body_height_profiles']+=1
    # ENTIRE actual exceptional profiles, independent of the primary sampler.
    small=[(1,[2],'onepart3'),(1,[3],'onepart4'),(2,[2],'onepart4'),(1,[2,2],'binary2'),(1,[2,2,2],'binary3')]
    opposites=[(a,[6]*r) for a in [1,2,7] for r in [5,6,7,8,9]]
    for a,U,kind in small:
        X=boxes(a,U)
        for b,V in opposites:
            Y=boxes(b,V);weight=len(Y)-1
            assert next(n for n in range(1,9) if at(Y,n)<2**(n-1))==7
            delta=64-Y[7];eta=2*Y[7]-Y[8];zeta=2*Y[8]-Y[9]
            assert delta>=1 and eta>=delta and zeta>=eta+1
            p=conv(X[::-1],Y[::-1]);E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
            d=[max(0,x-at(p,n-1)) for n,x in enumerate(p)];assert UI([x*2**n for n,x in enumerate(d)])
            if kind=='onepart3':L,R,B,H,critical=weight-3,weight+1,weight-3,1,[0,0,1,1]
            elif kind=='onepart4':L,R,B,H,critical=weight-2,weight+2,weight-2,1,[0,1,1,0]
            elif kind=='binary2':L,R,B,H,critical=weight-1,weight+2,weight-2,2,[1,2,0]
            elif eta==1:
                assert delta==1
                L,R,B,H,critical=weight-1,weight+2,weight-1,4,[3,4,2]
            else:
                assert UI([max(0,x) for x in E]);continue
            assert E[L+1:R+1]==critical
            assert min(E[:L+1])>=1 and UI(E[:L+1]) and min(E[1:B+1])>=H
            assert max(E[R+1:],default=0)<=0
            nu=len(p)-1-p[::-1].index(max(p));assert nu<L
            for t in [4,5,weight-7,weight,weight+1]:
                assert R<=t+B
                W=win(E,t);assert UI([max(0,x) for x in W])
                ct['independent_complete_exceptional_source_windows']+=1
            ct['independent_ENTIRE_source_profile_'+kind]+=1
    for j in range(16):
        a,b=1+j%2,1+j%3
        U=[2]*(j%4)+[3]*(1+j%2)+[4]*(1+j%2)
        V=[2]*(j%5)+[3]*(1+(j+1)%2)+[4]*(1+j%2)
        for W in [U,V]:
            W.append(max(5,2*sum(v for v in W if v>=3)))
            W.append(2*sum(v for v in W if v>=3))
        if j%4==0:
            if a+sum(U)<b+sum(V):a,b,U,V=b,a,V,U
            U=U+[max(U)+2];ct['independent_extra_heavier_append_originals']+=1
        M=max(U+V)+1;X,Y=boxes(a,U),boxes(b,V);H,L,R=core(X,Y,M)
        host=[1]*a+U+[M]+list(reversed([1]*b+V));actual=greedy_ideal(host)
        assert actual==H and UI(actual)
        ct['independent_TRUE_greedy_BOTH_two_dominant_originals']+=1
        ct['independent_TRUE_greedy_ORIGINAL_rank_counts']+=len(actual)
    X,Y=boxes(1,[2]),boxes(1,[6]*5);p=conv(X[::-1],Y[::-1]);E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
    weight=len(Y)-1;assert win(E,3)[weight-1:weight+2]==[3,1,2]
    local=['kappa_seven_legal_window_original_criterion_proof.tex','GeneralFiniteSourcePatch.lean','GeneralFiniteSourcePatch.log',
        'KappaSevenWindowRepair.lean','KappaSevenWindowRepair.log','KappaSevenOwnerCertificate.lean','KappaSevenOwnerCertificate.log',
        'build_kappa_seven_owner_certificate.py','kappa_seven_owner_certificate_data.json',
        'audit_kappa_seven_original_window_criterion.py','audit_kappa_seven_original_window_criterion.json','verify_kappa_seven_original_window_criterion.py']
    deps=['kappa_six_original_window_criterion_verification.json','kappa_six_legal_window_original_criterion_proof.tex','KappaSixWindowRepair.lean','KappaSixWindowRepair.log',
        'source_birth_gap_nonrecovery.tex','SourceBirthGapNonrecovery.lean','SourceBirthGapNonrecovery.log',
        'audit_source_birth_gap_complement.json','verify_source_birth_gap_complement.json',
        'source_birth_gap_refinements.tex','SourceBirthGapRefinements.lean','SourceBirthGapRefinements.log',
        'audit_source_birth_gap_refinements.json','verify_source_birth_gap_refinements.json',
        'arbitrary_source_gap_finite_owner.tex','ArbitrarySourceGapFiniteOwner.lean','ArbitrarySourceGapFiniteOwner.log',
        'C_to_coupled_S_rising_window.tex','agent_bothdeclining_first_birth.tex','agent_half_lc_actual_weak_curvature.tex',
        'binary_ternary_A2_original_family_verification.json','binary_ternary_A2_original_family_proof.tex',
        'complete_capacity_four_verification.json','complete_capacity_four_C_original_proof.tex',
        'relative_golden_head_dominant_C_verification.json','relative_golden_head_dominant_C_proof.tex',
        'multitail_binary_prefix_finite_principle_verification.json','multitail_binary_prefix_finite_principle.tex',
        'inductive_signed_window.tex','short_prefix_reflection_join.tex','verify_binary_ternary_A2_original_family.py']
    for name in [n for n in deps if n.endswith('_verification.json')]:
        dep=json.loads((SOURCE/name).read_text(encoding='utf8'))
        for n,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/n).read_bytes()).hexdigest()==digest,(name,n)
    primary=json.loads((ROOT/'audit_kappa_seven_original_window_criterion.json').read_text(encoding='utf8'))
    assert primary['status']=='PASS_EXACT_QA_KAPPA_SEVEN_LEGAL_WINDOW_COEFFICIENT_CRITERION'
    out=dict(status='PASS_FIRST_MISSING_SEVEN_LEGAL_WINDOW_FULL_A2_AND_ORIGINAL_A13_COEFFICIENT_CRITERION',new_scoped_reports=9,kernels=kernels,
        criterion='ANYfinaldeletionclosedACTUALFULLCclass/kappa<=7=>FULLpairA2/ORIGINALstrictCOREandBOTHrelativesANYstrictpeak+ONEarbitrarylegalheavierappend. RawsourceUI/THREEwindowUIat7remainFALSE. Four-or-longerwindowspositiveUI/initialsupportforBOTHnonrect.',
        complete_owners='OLDgap6h>=4/initialexchange-gap5alphaStar>=2/OLDfiniteownerboundd6D<=36 leaveEXACT341alpha1first2/h2or3owners. ALL853positivecurvatureedges reconstructed;851paidbyFIRST+SECONDcompulsorybirths,71distinctintegerobligationsONEkernelaggregate. ONLYunpaidbinary2/r0/C1 andbinary3/r0/C2. IndependentDEGREEpartitiongrammar/statehash/publicaggregateMATCH.',
        exceptions='CompleteFOURnewsourcepolynomialtypes:onepartweight3/onepartweight4/binary2/binary3eta=delta1. EveryENTIREpositiveUIprefix/strictLASTmodeedge/bodymin/criticalblock/sign-tailretained. Binary3c0=2<criticalheight4,soFIRSToutgoingedgeMUSTbeallowed;newgeneralpatchhandlesit. No sourceUIassumedacrossbadpatch.',
        general_patch='NEWunboundedfiniteHEIGHT/WIDTHcoefficientrepair:positiveUIprefix0..L,E>=0throughRthen<=0,bodyE>=Hon1..B,criticalE<=HonL+1..R,andR<=t+B =>WHOLEpositiveuniformwindowUI/initialsupport. ExactglobalNoRev/firstoutgoingexception/signedtail/clipping/wholefiniteupdownKERNELchecked. NoCUMULATIVELC-to-coefficientinference.',
        legality='NEWexceptionalownerweight<=7,oppositekappa7weight>=21:heavierappendforces t>=b-a>=14 ORlegalsortedappendtokappa7arm t>=6. ThusALLnewexceptionsuse>=4windows;maxkappa<=6usesfrozen3repair. Actualt3counterX1/2,Y1/6^5window3,1,2retained.',
        original_A13='A13=A12 UNIONALLmax4prefixT1T2 withT1>=max5,2W0/T2>=2(W0+T1) UNIONmaxcap6/nonbinaryweight<=32arms. ALLuniformFULLC/kappa<=7/finaldeletionclosed. BOTHarmsmayhaveTWOindependentdominantjumps/nooldweightorder;ORIGINALCORE/BOTHrelativesANYstrictpeak+ONEfurtherlegalheavierappend. NOamplification.',
        formal_scope='NINEnewreports:THREEgenericunboundedHEIGHT/WIDTHsourcepatchkernels+FIVEcompleteowner/source/mode/read/legalguardkernels+ONEordinarykernelaggregateALL71finiteownerproofmargins. NEWfinitepremiseEXPLICITCOMPLETE341owner/853edges/2exceptions. Actualinitialexchange/gap/finiteowner/sourceprofile/oldC-A1-Q/FULLA2/originalassemblyWRITTENandFROZENoldinputsreused,NOTendtoendLeancompositions. GeneralFiniteSourcePatch importsfrozenKappaSix;recompileold.oleanfirstwithoutoverwritingold.log. ExtraQAONLY.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',finite_proof_counts=finite_counts,finite_state_sha256=finite_sha,
        next='GeneralHEIGHT/WIDTHpatchforhigherfirstmissingweightsandgeneralhighercapacityC. GeneraloriginalobjectiveNOTcomplete.',
        independent_counts=dict(ct),primary_QA=primary['counts'],seconds=time.monotonic()-st,
        local_files=local,dependency_files=deps,sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'kappa_seven_original_window_criterion_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['kernels','sha256','local_files','dependency_files']}),flush=True)
if __name__=='__main__':main()
