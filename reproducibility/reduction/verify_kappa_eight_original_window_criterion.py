"""Independent COMPLETE degree-partition owner proof inputs, actual profiles, originals."""
from pathlib import Path
from collections import Counter
from random import Random
import sys,json,time,re,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_binary_ternary_A2_original_family import boxes,conv,UI,core,greedy_ideal
def at(p,n):return p[n] if 0<=n<len(p) else 0
def win(p,t):return [sum(at(p,n-j) for j in range(t)) for n in range(len(p)+t-1)]
def reports(name,count):
    src=(ROOT/(name+'.lean')).read_text(encoding='utf8');log=(ROOT/(name+'.log')).read_text(encoding='utf8')
    assert not any(x in src for x in ['native_decide','sorry','axiom '])
    assert not any(x in log for x in ['warning:','error:','sorryAx','ofReduceBool','failed'])
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==count
    out={n:[x.strip() for x in v.split(',') if x.strip()] for n,v in rows}
    assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in out.values())
    return out
def main():
    st=time.monotonic();ct=Counter();integers=set();states={};exceptions=[];sha=hashlib.sha256()
    data=json.loads((ROOT/'kappa_eight_owner_certificate_data.json').read_text(encoding='utf8'))
    # Independent degree-partition grammar: increments p<=q<=r, p<=alpha.
    for alpha in [1,2]:
        for D in range(2,(56 if alpha==1 else 36)+1):
            parts=[]
            for p in range(1,D):
                q=D-p
                if p<=q and p<=alpha:parts.append([p,q])
                for q in range(p,D-p):
                    r=D-p-q
                    if p<=q<=r and p<=alpha:parts.append([p,q,r])
            for ds in parts:
                U=[d+1 for d in ds];A=boxes(alpha,U);a=len(A)-1;q=A[::-1]
                s=[v-at(q,r-1) for r,v in enumerate(q)];rows=[]
                for r in range(a):
                    C=s[r+1]-s[r]
                    if s[r]<0 or C<=0:continue
                    n=a-r-7
                    pay=at(A,n)+at(A,n-2)+2*at(A,n-3)+4*at(A,n-4)+8*at(A,n-5)
                    margin=pay-C;row=dict(r=r,curvature=C,birth_index=n,payment=pay,margin=margin)
                    rows.append(row);ct['all_positive_curvature_edges']+=1
                    if margin<0:
                        exceptions.append(dict(alpha=alpha,U=U,D=D,weight=a,**row));ct['unpaid_exception_edges']+=1
                    else:integers.add(margin);ct['kernel_payment_obligations']+=1
                state=dict(alpha=alpha,U=U,D=D,weight=a,forward=A,reverse=q,ALL_curvature_rows=rows)
                key=(alpha,tuple(U));assert key not in states;states[key]=state;ct['complete_owner_states']+=1
    assert len(states)==1441 and len(exceptions)==6 and dict(ct)==data['counts']
    assert {(x['alpha'],tuple(x['U'])) for x in data['states']}==set(states)
    for state in data['states']:
        assert states[(state['alpha'],tuple(state['U']))]==state
        sha.update(json.dumps(state,separators=(',',':')).encode())
    assert sha.hexdigest()==data['state_sha256']
    key=lambda x:(x['alpha'],x['U'],x['r'])
    assert sorted(exceptions,key=key)==sorted(data['exceptions'],key=key)
    values=sorted(integers);assert values==data['integer_margins'] and len(values)==694
    src=(ROOT/'KappaEightOwnerCertificate.lean').read_text(encoding='utf8');exprs=[];chunks=[]
    for i in range(0,len(values),140):
        name='chunk_'+str(i//140);chunks.append(name)
        expr=' && '.join(f'decide ((0 : Int) ≤ {v})' for v in values[i:i+140]);exprs.append('('+expr+')')
        assert 'private theorem '+name+' : ('+expr+') = true := by decide' in src
    public='theorem complete_all_owner_payments : ('+' && '.join(exprs)+') = true := by\n  simp only ['+', '.join(chunks+['Bool.and_self'])+']'
    assert public in src and len(chunks)==5
    finite_ct=dict(ct);finite_sha=sha.hexdigest()
    kernels={'KappaEightWindowRepair':reports('KappaEightWindowRepair',5),
        'KappaEightOwnerCertificate':reports('KappaEightOwnerCertificate',1)}
    # Separate complete actual-polynomial source profiles from positive suffix boxes.
    small=[(1,[2]),(1,[3]),(1,[4]),(2,[3]),(1,[2,2]),(1,[2,3]),(2,[2,2]),
        (1,[2,2,2]),(1,[2,2,3]),(2,[2,2,2])]
    opposites=[(a,[7]*h) for a in [1,4,11] for h in [6,7,8,10]]
    opposites += [(1,[2,3,4,5,6,7]),(2,[2,2,3,4,5,6,7])]
    for alpha,U in small:
        X=boxes(alpha,U);a=len(X)-1
        for beta,V in opposites:
            Y=boxes(beta,V);b=len(Y)-1
            assert next(n for n in range(1,10) if at(Y,n)<2**(n-1))==8
            delta=128-Y[8];eta=2*Y[8]-Y[9];zeta=2*Y[9]-Y[10]
            assert 1<=delta<=eta and zeta>=eta+1
            p=conv(X[::-1],Y[::-1]);E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
            d=[max(0,x-at(p,n-1)) for n,x in enumerate(p)];assert UI([x<<n for n,x in enumerate(d)])
            if len(U)==1:
                L=b+a-7;m=min(alpha+1,U[0]);R=b+m-1;B=L;H=1
                critical=[0]*(b-1-L)+[1]*m
            elif len(U)==2:
                L=b+a-7;R=b+(1 if a==5 else 2);B=L-1;H=2
                critical=[0,1,2] if a==5 else [1,2,1]
                assert E[L-1]==delta+eta
            elif a==7 and delta==1:
                L=b-1;R=b+2;B=b-2;H=3;critical=[2,3,2]
                assert E[L]==delta+eta and E[L-1]==zeta+eta+2
            elif a==8 and eta==1:
                assert delta==1
                L=b-1;R=b+3;B=b-1;H=4;critical=[3,4,3,int(alpha==1)]
                assert E[L]==zeta+3
            else:
                assert UI([max(0,x) for x in E]);ct['independent_three_part_paid_source_cones']+=1;continue
            assert E[L+1:R+1]==critical and UI(E[:L+1]) and min(E[:L+1])>=1
            assert min(E[1:B+1])>=H and max(E[R+1:],default=0)<=0
            nu=len(p)-1-p[::-1].index(max(p));assert nu<L
            for t in sorted(set([5,8,max(5,b-a),b-1,b+2])):
                assert R<=t+B;w=[max(0,x) for x in win(E,t)];assert UI(w)
                pos=[j for j,x in enumerate(w) if x>0];assert pos==list(range(pos[-1]+1))
                ct['independent_entire_exceptional_source_windows']+=1
            ct['independent_entire_source_profiles']+=1
    for j in range(12):
        a,b=1+j%3,1+j%2
        U=[2]*(j%3)+[3]+[4]*(1+j%2);V=[2]*(j%4)+[3]*(1+j%2)+[4]
        for word in [U,V]:
            for _ in range(3):word.append(max(5,2*sum(x for x in word if x>=3)))
        if j%4==0:
            if a+sum(U)<b+sum(V):a,b,U,V=b,a,V,U
            U=U+[max(U)+2];ct['independent_extra_heavier_append_originals']+=1
        M=max(U+V)+1;X,Y=boxes(a,U),boxes(b,V);H,L,R=core(X,Y,M)
        host=[1]*a+U+[M]+list(reversed([1]*b+V));actual=greedy_ideal(host)
        assert actual==H and all(UI(p) for p in [actual,L,R])
        ct['independent_TRUE_greedy_BOTH_three_dominant_originals']+=1
        ct['independent_TRUE_greedy_ORIGINAL_rank_counts']+=len(actual)
        ct['independent_BOTH_relative_polynomials']+=2
    X,Y=boxes(1,[2]),boxes(1,[7]*6);p=conv(X[::-1],Y[::-1]);E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
    b=len(Y)-1;assert win(E,4)[b-1:b+2]==[3,1,2]
    local=['kappa_eight_legal_window_original_criterion_proof.tex','KappaEightWindowRepair.lean','KappaEightWindowRepair.log',
        'KappaEightOwnerCertificate.lean','KappaEightOwnerCertificate.log','build_kappa_eight_owner_certificate.py',
        'kappa_eight_owner_certificate_data.json','audit_kappa_eight_original_window_criterion.py',
        'audit_kappa_eight_original_window_criterion.json','verify_kappa_eight_original_window_criterion.py']
    deps=['kappa_seven_original_window_criterion_verification.json','kappa_seven_legal_window_original_criterion_proof.tex',
        'GeneralFiniteSourcePatch.lean','GeneralFiniteSourcePatch.log',
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
    primary=json.loads((ROOT/'audit_kappa_eight_original_window_criterion.json').read_text(encoding='utf8'))
    assert primary['status']=='PASS_EXACT_QA_KAPPA_EIGHT_LEGAL_WINDOW_COEFFICIENT_CRITERION'
    out=dict(status='PASS_FIRST_MISSING_EIGHT_LEGAL_WINDOW_FULL_A2_AND_ORIGINAL_A14_COEFFICIENT_CRITERION',
        new_scoped_reports=6,kernels=kernels,
        criterion='ANYfinaldeletionclosedACTUALFULLCclass/kappa<=8=>FULLpairA2/ORIGINALstrictCOREandBOTHrelativesANYstrictpeak+ONEarbitrarylegalheavierappend. BOTHnonrectsourcesALLt>=5windowspositiveUI/initialsupport. RawsourceUI/FOURwindowUIremainFALSE.',
        complete_owners='OLDabsolute8h>=4/initialexchangegap5alphaStar>=3/finiteownerD<=56(alpha1)or36(alpha2)=>COMPLETE1441canonicalh2/h3owners/4457curvatureedges. SIXcompulsorysourceweights[1,0,1,2,4,8]pay4451;ONLYsixr0exceptionsweight5..8. ALL694integerobligationsFIVEchunksONEcompletekernelaggregate;independentdegreepartitionsALLstates/edges/exceptions/hash/publicobligationsMATCH.',
        exceptions='TENnewpolynomialtypes:FOURonepartweight3..5/THREEtwo-partweight5..6/THREEthree-partweight7..8. Negative-r=-1exceptionALSOretainedforbinary2weight5. Three-part7onlydelta1/three-part8onlyeta=delta1. ENTIREpositiveUIprefix/strictLASTmode/body/critical/sign-tailverified;heights1/2/3/4,bodyexcludesE0=2whenheight>2.',
        window_repair='FROZENarbitraryHEIGHT/WIDTHpatchappliedtoALLTENprofiles:body>=Hon1..B,critical<=HonL+1..R,R<=t+Bforallt>=5. WHOLEpositivewindowUI/initialsupport,firstoutgoingedgeunconstrained. GenericTHREEkernelsREUSEDNOTrecounted. ActualX1/2,Y1/7^6FOURwindowcounter3,1,2retained.',
        legality='ALLnewexceptionownersweight<=8,oppositekappa8weight>=28:appendownert>=b-a>=20 ORappendkappa8armt>=7;thusALLnewexceptionlegalwindows>=5. OLDmaxkappa<=7subclassusesfrozenarbitraryheavierappendcorollaryincludingSHORTERwindows.',
        original_A14='A14=A13 UNIONALLmax4prefixT1T2T3 withT1>=max5,2W0,T2>=2(W0+T1),T3>=2(W0+T1+T2) UNIONmaxcap7/nonbinaryweight<=32arms. ALLuniformFULLC/kappa<=8/finaldeletionclosed. BOTHarmsTHREEindependentdominantjumps/nooldweightorder;ORIGINALCORE+BOTHrelativesANYstrictpeak+ONEfurtherlegalheavierappend;NOamplification.',
        formal_scope='SIXnewreports:FIVEcompleteowner/source/mode/body/read/legalguardkernels+ONEordinarykernelaggregateALL694finiteownerproofmargins. NEWfinitepremiseEXPLICITCOMPLETE1441owner/4457edge/6exceptionclassification. GenericGeneralFiniteSourcePatchTHREEreportsREUSED;oldinitialexchange/gap/source/finiteowner/C-A1-Q/FULLA2/originalassembliesWRITTEN/frozen,NOTendtoendLeancompositions. Extraactual/originalQAONLY.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',finite_proof_counts=finite_ct,finite_state_sha256=finite_sha,
        independent_counts=dict(ct),primary_QA=primary['counts'],seconds=time.monotonic()-st,
        local_files=local,dependency_files=deps,
        sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'kappa_eight_original_window_criterion_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['kernels','sha256','local_files','dependency_files']}),flush=True)
if __name__=='__main__':main()
