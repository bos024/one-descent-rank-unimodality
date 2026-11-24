"""Independent maximum-part owner grammar, product-ratio ranks, actual source/window model."""
from pathlib import Path
from fractions import Fraction
from collections import Counter
import sys,json,re,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_binary_ternary_A2_original_family import boxes,conv,UI,core,greedy_ideal
def at(p,n):return p[n] if 0<=n<len(p) else 0
def parts_max(n,h,cap):
    if h==1:
        if 1<=n<=cap:yield [n]
        return
    for largest in range((n+h-1)//h,min(cap,n-h+1)+1):
        for rest in parts_max(n-largest,h-1,largest):yield rest+[largest]
def ratio_product(r,e,m):
    if not 0<=m<=r:return Fraction(0)
    p=Fraction(1)
    for i in range(m):p*=Fraction(r-i,r+e+3+i)
    return p
def win(p,t):
    # Independent cumulative difference rather than primary rolling window.
    C=[0]
    for x in p:C.append(C[-1]+x)
    def cs(n):return C[min(max(0,n+1),len(p))]
    return [cs(n)-cs(n-t) for n in range(len(p)+t-1)]
def weightedD(p):return [max(0,x-at(p,n-1))<<n for n,x in enumerate(p)]
def reports(name,count):
    src=(ROOT/(name+'.lean')).read_text(encoding='utf8');log=(ROOT/(name+'.log')).read_text(encoding='utf8')
    assert not any(x in src for x in ['native_decide','sorry','axiom '])
    assert not any(x in log for x in ['warning:','error:','sorryAx','ofReduceBool','failed'])
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==count
    out={n:[x.strip() for x in v.split(',') if x.strip()] for n,v in rows}
    assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in out.values());return out
def main():
    st=time.monotonic();ct=Counter();ranks={};states={};rows={};exceptions=[];integers=set();sha=hashlib.sha256()
    data=json.loads((ROOT/'kappa_nine_head_certificate_data.json').read_text(encoding='utf8'))
    # Independent enumeration by DEGREE, then reverse rank; source ratios are products.
    for alpha in [1,2,3]:
        d=9-alpha
        for D in range(2,min(2*d*(d-3),12*d-25)+1):
            for r in range((D-2)//2+1):
                e=D-2*r-2
                if e>d-3:continue
                L=d-e-3
                p=ratio_product(r,e,L)+sum(Fraction(2**(j-2))*ratio_product(r,e,L+j) for j in range(2,7))-Fraction(e+1,r+1)
                paid=p>=0
                rank=dict(alpha=alpha,d=d,e=e,r=r,D=D,numerator=p.numerator,denominator=p.denominator,paid=paid)
                ranks[(alpha,D,r)]=rank;ct['complete_rank_states']+=1
                if paid:
                    integers.update([p.numerator,p.denominator-1]);ct['rational_rank_states_paid']+=1;continue
                ct['unpaid_rank_states']+=1
                for h in range(2,min(D,3 if alpha==3 else 5)+1):
                    for ds in parts_max(D,h,D):
                        if ds[0]>alpha:continue
                        U=[x+1 for x in ds];key=(alpha,tuple(U))
                        if key not in states:
                            A=boxes(alpha,U);states[key]=dict(alpha=alpha,U=U,D=D,weight=len(A)-1,forward=A,reverse=A[::-1])
                        state=states[key];A=state['forward'];q=state['reverse'];a=len(A)-1
                        sr=at(q,r)-at(q,r-1);C=at(q,r+1)-2*at(q,r)+at(q,r-1);j=a-r;n=j-8
                        pay=at(A,n)+at(A,n-2)+2*at(A,n-3)+4*at(A,n-4)+8*at(A,n-5)+16*at(A,n-6)
                        row=dict(alpha=alpha,U=U,D=D,r=r,primitive=sr,curvature=C,shared_rank=j,birth_index=n,payment=pay)
                        ct['complete_owner_rank_inputs']+=1
                        if sr<0:kind='negative_primitive';margin=-sr-1;ct['noncritical_negative_primitive']+=1
                        elif C<=0:kind='nonpositive_curvature';margin=-C;ct['noncritical_nonpositive_curvature']+=1
                        else:
                            ct['positive_curvature_owner_rank_inputs']+=1
                            assert C<=pay or j<=10
                            if C<=pay:kind='source_paid';margin=pay-C;ct['direct_source_owner_payments']+=1
                            else:
                                kind='strict_head';margin=10-j;ct['unpaid_positive_curvature_edges']+=1
                                exceptions.append(dict(alpha=alpha,U=U,weight=a,D=D,r=r,curvature=C,shared_rank=j,payment=pay))
                        row.update(kind=kind,margin=margin);integers.add(margin);rows[(alpha,tuple(U),r)]=row
    ct['distinct_canonical_owners']=len(states)
    assert dict(ct)==data['counts'] and len(ranks)==406 and len(rows)==4377 and len(states)==2143
    assert len(exceptions)==19 and max(x['shared_rank'] for x in exceptions)==10
    assert max(x['D'] for x in ranks.values() if not x['paid'])==25
    for rank in data['ranks']:
        assert rank==ranks[(rank['alpha'],rank['D'],rank['r'])]
        sha.update(json.dumps(rank,separators=(',',':')).encode())
    for state in data['states']:
        assert state==states[(state['alpha'],tuple(state['U']))]
        sha.update(json.dumps(state,separators=(',',':')).encode())
    for row in data['ALL_owner_rank_rows']:
        assert row==rows[(row['alpha'],tuple(row['U']),row['r'])]
        sha.update(json.dumps(row,separators=(',',':')).encode())
    assert sha.hexdigest()==data['state_sha256']
    key=lambda x:(x['alpha'],x['U'],x['r'])
    assert sorted(exceptions,key=key)==sorted(data['exceptions'],key=key)
    vals=sorted(integers);assert vals==data['integer_margins'] and len(vals)==719
    src=(ROOT/'KappaNineHeadCertificate.lean').read_text(encoding='utf8');chunks=[];exprs=[]
    for i in range(0,len(vals),120):
        name='chunk_'+str(i//120);chunks.append(name)
        expr=' && '.join(f'decide ((0 : Int) ≤ {v})' for v in vals[i:i+120]);exprs.append('('+expr+')')
        assert 'private theorem '+name+' : ('+expr+') = true := by decide' in src
    public='theorem complete_all_rank_source_or_head_obligations : ('+' && '.join(exprs)+') = true := by\n  simp only ['+', '.join(chunks+['Bool.and_self'])+']'
    assert public in src and len(chunks)==6
    finite_counts=dict(ct);finite_sha=sha.hexdigest()
    kernels={'CoupledSourceWindowA2':reports('CoupledSourceWindowA2',9),'KappaNineHeadCertificate':reports('KappaNineHeadCertificate',1)}
    # Genuine actual opposite derivative and retained main CI, not differentiation of a bound.
    opposite=[(1,list(range(2,9))),(1,[8]*7),(5,[8]*8),(100,[8]*7),
        (1,list(range(2,8))+[1000]),(3,[2]*9+list(range(3,9)))]
    for beta,V in opposite:
        Y=boxes(beta,V);q=Y[::-1];L=[1]* (beta+1)
        for v in V:L=conv(L,[1]*v)
        Dmain=len(L)-1;B=max([beta]+[v-1 for v in V])
        assert Dmain>=29 and Dmain-B>=22
        for n in range(15):
            assert at(q,n)-at(q,n-1)>=at(L,n)-at(L,n-1)>=1
            ct['independent_ACTUAL_opposite_strict_head_derivatives']+=1
    owner_profiles={(x['alpha'],tuple(x['U'])) for x in exceptions}
    owner_profiles|={(1,(2,)),(1,(3,)),(2,(3,)),(2,(4,))}
    for alpha,U in sorted(owner_profiles):
        X=boxes(alpha,list(U))
        for beta,V in opposite[:3]:
            Y=boxes(beta,V);p=conv(X[::-1],Y[::-1]);D=len(p)-1;f=weightedD(p);assert UI(f)
            E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
            m=D-p[::-1].index(max(p));ell=f.index(max(f))
            for n in range(m+1,len(p)):
                T=E[n+1]-E[n]
                if E[n]<0 or T<=0:continue
                j=D-n;assert j<=10;ct['independent_positive_Q_recoveries_shared_rank_bound']+=1
                for k in range(max(0,j-2)):
                    if k>=ell or p[n]<=p[k] or at(p,n+1)<=p[k+1] or E[n]>E[k]:continue
                    assert T<=E[k+1]-E[k];ct['independent_ALL_proper_closed_heads_paid']+=1
                    if E[n]==E[k]:ct['independent_EQUAL_source_heads_paid']+=1
            u=[max(0,x-at(p,n-1)) for n,x in enumerate(p)]
            for t in [1,2,3,4,5,6,9,14,29]:
                Vp=win(p,t);fnew=weightedD(Vp);assert UI(fnew)
                c=max(m,t-1)
                g=([x<<n for n,x in enumerate(win(u,t))] if m>=t-1 else [x<<n for n,x in enumerate(p)])
                assert UI(g) and all(at(fnew,n)==at(g,n) for n in range(c+1))
                assert at(fnew,c+1)<=at(g,c+1)
                for n in range(c,len(fnew)-2):
                    if fnew[n+1]<=fnew[n]:assert fnew[n+2]<=fnew[n+1]
                ct['independent_FULL_window_A2_head_boundary_closed_cross_checks']+=1
    for j in range(8):
        a,b=1+j%3,1+j%2;U=[2]*(j%3)+[3]+[4];V=[2]*(j%4)+[3]+[4]*(1+j%2)
        for word in [U,V]:
            for _ in range(4):word.append(max(5,2*sum(v for v in word if v>=3)))
        if j%4==0:
            if a+sum(U)<b+sum(V):a,b,U,V=b,a,V,U
            U=U+[max(U)+2];ct['independent_extra_heavier_append_originals']+=1
        M=max(U+V)+1;X,Y=boxes(a,U),boxes(b,V);H,L,R=core(X,Y,M)
        host=[1]*a+U+[M]+list(reversed([1]*b+V));actual=greedy_ideal(host)
        assert actual==H and all(UI(p) for p in [actual,L,R])
        ct['independent_TRUE_greedy_BOTH_four_dominant_originals']+=1
        ct['independent_TRUE_greedy_ORIGINAL_rank_counts']+=len(actual);ct['independent_BOTH_relative_polynomials']+=2
    local=['coupled_source_window_A2_and_kappa_nine_original_proof.tex','CoupledSourceWindowA2.lean','CoupledSourceWindowA2.log',
        'KappaNineHeadCertificate.lean','KappaNineHeadCertificate.log','build_kappa_nine_head_certificate.py',
        'kappa_nine_head_certificate_data.json','audit_coupled_source_kappa_nine.py','audit_coupled_source_kappa_nine.json',
        'verify_coupled_source_kappa_nine.py']
    deps=['kappa_eight_original_window_criterion_verification.json','kappa_eight_legal_window_original_criterion_proof.tex',
        'first_missing_product_mode_verification.json','first_missing_product_mode_and_one_part_window_proof.tex',
        'kappa_nine_source_nonrecovery.tex','KappaNineSourceNonrecovery.lean','KappaNineSourceNonrecovery.log',
        'probe_kappa_nine_source_complement.py','probe_kappa_nine_source_complement.json',
        'verify_kappa_nine_source_complement.py','verify_kappa_nine_source_complement.json',
        'source_birth_gap_nonrecovery.tex','source_birth_gap_refinements.tex','arbitrary_source_gap_finite_owner.tex',
        'source_curvature_linear_owner.tex','SourceCurvatureLinearOwner.lean','SourceCurvatureLinearOwner.log',
        'mixed_head_raw_primitive_LC.tex','MixedHeadRawPrimitiveLC.lean','MixedHeadRawPrimitiveLC.log',
        'agent_mixed_strict_head_74.tex','agent_mixed_strict_head_74.lean','agent_mixed_strict_head_74.log',
        'agent_mixed_strict_head_74_verification.json',
        'C_to_coupled_S_rising_window.tex','agent_bothdeclining_first_birth.tex','agent_half_lc_actual_weak_curvature.tex',
        'binary_geometric_differences.tex','clipped_forward_ratio_frontier.tex',
        'binary_ternary_A2_original_family_verification.json','binary_ternary_A2_original_family_proof.tex',
        'complete_capacity_four_verification.json','complete_capacity_four_C_original_proof.tex',
        'relative_golden_head_dominant_C_verification.json','relative_golden_head_dominant_C_proof.tex',
        'multitail_binary_prefix_finite_principle_verification.json','multitail_binary_prefix_finite_principle.tex',
        'inductive_signed_window.tex','short_prefix_reflection_join.tex','verify_binary_ternary_A2_original_family.py']
    for name in [n for n in deps if n.endswith('_verification.json')]:
        dep=json.loads((SOURCE/name).read_text(encoding='utf8'))
        for n,digest in dep.get('sha256',{}).items():assert hashlib.sha256((SOURCE/n).read_bytes()).hexdigest()==digest,(name,n)
    primary=json.loads((ROOT/'audit_coupled_source_kappa_nine.json').read_text(encoding='utf8'))
    assert primary['status']=='PASS_EXACT_QA_CLOSED_SOURCE_WINDOW_A2_AND_KAPPA_NINE_ORIGINAL'
    out=dict(status='PASS_CLOSED_SOURCE_FULL_WINDOW_A2_AND_KAPPA_NINE_ORIGINAL_A15_CRITERION',
        new_scoped_reports=10,kernels=kernels,
        criterion='ANYfinaldeletionclosedACTUALFULLCclass/kappa<=9=>FULLpairA2/ORIGINALstrictCORE+BOTHrelativesANYstrictpeak+ONEarbitrarylegalheavierappend. NoAMPLIFICATION. Oldmax<=8usesfrozenextraappend;oldmax9usesNEWproperCLOSED-gapS-to-FULLweighted-windowA2.',
        complete_certificate='COMPLETE406canonicalrankstatesafterh>=6absolute9/h4gap6/h2gap5/exchange/finiteownerbounds. 291RATIONALsourcepaid,115unpaidD<=25. ALL2143canonicalowners/4377owner-rankinputs/3757nonpositivecurvature/620positive/601directsourcepaid/ONLY19unpaidcandidatesALLj<=10. ALL719integerobligationsSIXchunksONEpublickernelaggregate. IndependentDEGREE/MAXIMUM-partgrammar/PRODUCT-fractionratios reconstructALLstates/categories/hash/publicobligations.',
        closed_window_bridge='NEWUNBOUNDEDS-to-FULLwindowA2:FULLoldA2+A1+properSforCLOSED0<=E_n<=E_k=>EVERY[t]p FULLweighted-positive-DUI. WHOLEUIheadcomparisoncutc=max(oldLASTmode,t-1)usesLCgeometrickernelORoldA1;firstboundarydominated. Nonstrictfallspropagatebyclosedsourcepayment/negativeA1tail/oldgeometrictailbudget. COMPLETEglobalNoRevkernelincludesEQUALITYandplateaus. NOTwholeRAW-source-windowUI.',
        strict_head='ANYnewK9positiveQrecoveryj<=10,negative-rbirthmissa<=6=>j<=7. BOTHproperwindows=>k+1<=j-2<=8and<=a-1. GenuineoppositemainCI M>=29/otherdegree>=22 givesACTUALDeltaqY>=1through14;ALLrawownerusedcoeffnonnegative. ONEconvolutionterm paysABSOLUTEr<k;OLDrelativeRAWkernelhas+1SURPLUSandthereforealsopaysCLOSEDgapE_n=E_k. Both-risingC/both-nonrisingactualgivetailT<=0. FULLoldA2paysH>=0fornonpositiveT.',
        original_A15='A15=A14 UNIONALLmax4prefixFOURdominantcapacitiesT_i>=2(W0+sumpreviousT),T1>=max5,2W0 UNIONmaxcap8/nonbinaryweight<=32arms. ALLuniformFULLC/kappa<=9/deletionclosed. BOTHarmsFOURindependentdominantjumps/ANYstrictpeak+ONEextraarbitrarylegalheavierappend;ORIGINALCOREandBOTHrelativescoefficientsUI.',
        formal_scope='TENnewstandardaxiomreports:NINEclosed-source/negative-tail/WHOLEfinitegeometricbudget/relative+1equality/WHOLEhead-boundary-crossNoRev/headselection/properheadguardkernels+ONEcompletefiniteaggregateALL719rational/owner/category/headobligations. EXPLICITnewfinitepremise406ranks/2143owners/4377inputs. ActualS-to-windowLCkernel/model/gap/CI/C-A1-Q/A2/originalassembliesWRITTENandfrozeninputsreused,NOTendtoendLeancompositions. Extraactual/greedyQAONLY.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',finite_proof_counts=finite_counts,finite_state_sha256=finite_sha,
        independent_counts=dict(ct),primary_QA=primary['counts'],seconds=time.monotonic()-st,
        local_files=local,dependency_files=deps,
        sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'coupled_source_kappa_nine_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['kernels','sha256','local_files','dependency_files']}),flush=True)
if __name__=='__main__':main()
