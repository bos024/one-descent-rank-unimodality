"""Independent positive suffix boxes, full small entrance, and Q(a) source bridge."""
from pathlib import Path
from itertools import accumulate
from collections import Counter
from random import Random
import sys,json,re,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
from verify_tribonacci_quadratic_inverse import ZERO,ONE,AA,BB,LAM,add,sub,mul,scale,raw,closed,integral,lower_alpha
from verify_tribonacci_rich_reverse_quotient import reverse_via_forward

def reports(name,count):
    src=(ROOT/(name+'.lean')).read_text(encoding='utf8');log=(ROOT/(name+'.log')).read_text(encoding='utf8')
    assert not any(v in log for v in ['warning:','error:','sorryAx','ofReduceBool','failed']) and 'native_decide' not in src
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==count
    out={}
    for n,rs in rows:
        a=[s.strip() for s in rs.split(',') if s.strip()];assert set(a)<={'propext','Classical.choice','Quot.sound'};out[n]=a
    return out

def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();data=json.loads((ROOT/'pure_ternary_complete_C_certificate_data.json').read_text())
    produced={(v['r'],v['alpha']):v for v in data['contexts']};keys={(r,a) for r in range(11,18) for a in range(1,r+1)}
    assert set(produced)==keys and len(keys)==98;values=set()
    for r,alpha in sorted(keys):
        F=suffix_boxes(alpha,[3]*r)[:alpha+3*r+2];D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
        L=D.index(max(D));assert L<=2*r;G=list(accumulate(F));ms=[];row=produced[r,alpha]
        for N in range(4,2*r+1):
            for k in range(1,N-2):
                m=G[k]*D[N-1]-G[k-1]*D[N];assert m>=0;ms.append(m);values.add(m)
        assert F==row['F'] and D==row['D'] and L==row['mode'] and ms==row['literal_C_margins']
        ct['COMPLETE_independent_small_entrance_hosts']+=1;ct['COMPLETE_independent_LITERAL_integer_C_products']+=len(ms)
        sha.update(str((r,alpha,F,D,ms)).encode())
    assert sorted(values)==data['unique_margins'] and len(values)==16115
    lean=(ROOT/'PureTernaryCompleteCCertificate.lean').read_text(encoding='utf8')
    lists=re.findall(r'^def part\d+ : List ℤ := \[([^\]]*)\]$',lean,re.M)
    assert [int(x.strip()) for row in lists for x in row.split(',')]==sorted(values) and len(lists)==54
    for r in range(11,18):
        A=suffix_boxes(r,[3]*r);B=suffix_boxes(r+37,[3]*r);assert A[:2*r+1]==B[:2*r+1]
        ct['independent_padding_representative_prefix_controls']+=1
    root=json.loads((SOURCE/'tribonacci_rich_reverse_certificate_data.json').read_text());M=root['root_denominator'];NA=root['root_lower_numerator']-M
    def sign(v):
        if v==ZERO:return 0
        if lower_alpha(integral(v),NA,M)>0:return 1
        assert lower_alpha(integral(scale(v,-1)),NA,M)>0
        return -1
    for r in [18,19,20,24,35,50,80]:
        E=closed(0,r);J,_=reverse_via_forward(E);H=len(J)-1;X={H:ZERO}
        for n in range(H-1,-2,-1):X[n]=mul(BB,add(X[n+1],J[n+1] if n+1>=0 else ZERO))
        # A finite padding larger than the support realizes the entire d-infinity.
        Fref=suffix_boxes(5*r,[3]*r);din=[max(0,Fref[n]-Fref[n-1]) for n in range(2,3*r+1)]
        for s in range(H+1):
            y=add(X.get(s,ZERO),X[s-1]);assert y==raw(din[r+s] if r+s<len(din) else 0)
            ct['independent_Qa_ACTUAL_future_quotient_identity_reads']+=1
        # The previous physical value is different: retain rather than erase it.
        yprev=add(X[-1],mul(BB,add(X[-1],J[0])))
        assert yprev!=raw(din[r-1]);ct['independent_nonzero_previous_physical_remainder_controls']+=1
        jm=0
        for n in range(1,len(J)):
            if sign(sub(J[n],J[jm]))>0:jm=n
        for n in range(r+1,len(din)+3):
            residual=sub(scale(LAM,din[n-1] if n-1<len(din) else 0),raw(din[n] if n<len(din) else 0))
            s=n-r;target=add(J[s] if 0<=s<len(J) else ZERO,J[s-1] if 0<=s-1<len(J) else ZERO)
            assert residual==target;ct['independent_FULL_residual_tail_identity_reads']+=1
        for alpha in [1,2,3,5,r,2*r]:
            Factual=suffix_boxes(alpha,[3]*r);D=[0,0]+[max(0,Factual[n]-Factual[n-1]) for n in range(2,len(Factual))]
            assert D.index(max(D))-2<=r+jm
            for n,v in enumerate(D[2:]):
                k=n-(alpha+r-1);loss=E[k] if 0<=k<len(E) else 0
                assert v==max(0,(din[n] if n<len(din) else 0)-loss)
                ct['independent_FULL_actual_padding_and_clipping_identity_reads']+=1
            ct['independent_actual_vs_J_FIRSTmode_controls']+=1
        sha.update(str((r,E,J,din,jm)).encode())
    rng=Random(20261101118)
    for r,alpha in [(r,a) for r in range(18,33) for a in [1,2,3,r,2*r]]+[(rng.randint(18,95),rng.randint(1,220)) for _ in range(175)]:
        F=suffix_boxes(alpha,[3]*r);D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];L=D.index(max(D));G=list(accumulate(F));A=r+2
        for n in range(A,L):assert D[n]**2>=D[n-1]*D[n+1];ct['independent_actual_PREmode_DLC_minors']+=1
        best=1
        for N in range(4,L+1):
            k=N-3
            if G[k]*G[best-1]<G[best]*G[k-1]:best=k
            assert G[best]*D[N-1]>=G[best-1]*D[N]
            ct['independent_actual_all_shift_prefix_minima']+=1;ct['independent_actual_logical_shifts']+=N-3
        ct['independent_actual_QA_hosts']+=1;sha.update(str((r,alpha,F,D,L)).encode())
    qa=json.loads((ROOT/'audit_pure_ternary_complete_C.json').read_text());assert qa['status']=='EXACT_QA_PASS_PURE_TERNARY_COMPLETE_C_UNDER_PROOF_AUDIT'
    local=['pure_ternary_complete_C_proof.tex','PureTernaryCompleteC.lean','PureTernaryCompleteC.log',
      'PureTernaryCompleteCCertificate.lean','PureTernaryCompleteCCertificate.log',
      'build_pure_ternary_complete_C_certificate.py','pure_ternary_complete_C_certificate_data.json',
      'audit_pure_ternary_complete_C.py','audit_pure_ternary_complete_C.json','verify_pure_ternary_complete_C.py']
    deps=['renewal_root_primitive_cut_verification.json','renewal_root_positive_primitive_cut_proof.tex',
      'tribonacci_quotient_primitive_verification.json','tribonacci_rich_reverse_quotient_verification.json',
      'tribonacci_rich_reverse_certificate_data.json','first_missing_renewal_envelope.tex',
      'finite_initial_ones_relative_derivative.tex','sharpened_forward_derivative_centers.tex',
      'TernaryRichCompleteC.lean','TernaryRichCompleteC.log','ternary_rich_complete_C_verification.json',
      'multitail_binary_prefix_finite_principle_verification.json','verify_subdegree_CI_entrance.py',
      'verify_tribonacci_quadratic_inverse.py','verify_tribonacci_rich_reverse_quotient.py']
    out=dict(status='PASS_ALL_COUNT_ALL_PADDING_PURE_TERNARY_ACTUAL_COMPLETE_C',new_scoped_reports=12,
      kernels={'PureTernaryCompleteC':reports('PureTernaryCompleteC',11),'PureTernaryCompleteCCertificate':reports('PureTernaryCompleteCCertificate',1)},
      theorem='EVERYACTUAL1alpha3r,ALLalpha>=1/r>=0:FULLC atEVERYcurrentN/EVERYshift>=3. Counts/padding/ranks/shiftsALLUNBOUNDED. NewACTUALfamily,notjustproperCIquotient.',
      derivative='ALLr>=18,ALLalpha:actualpositiveDordinaryLC atEVERYcentreN>=r+2STRICTLYBEFOREFIRSTDmode. TRUEd-infinity_(r+s)=future_bJ_s+future_bJ_(s-1)onlys>=0. PreviousphysicalvalueDIFFERSandseparatelypaid. ALLTHREEsourcecutstartupcentrespaid;degree-oneRRETAINEDoutsidecutband.',
      entry='Exactresidualnormb^n implies|h_n-lambda*hprev|<1ALLn>=3. FIRSTactualgrowthgaplambda*D_(r+2)-D_(r+3)>=r-4;correctTRUEordinaryFseedF_(r+1)-mu*F_r>=6forALLmu<=firstpostsourceDratio. D-LCratiochain+protectedreferenceG+TWOcumulativeintegrationsproveALLCshifts. DoesNOTassumeactualCDFLC.',
      entrance='COMPLETE98hosts11<=r<=17,1<=alpha<=r,EVERYN4..2r/EVERYk1..N-3:34062LITERALintegerCproducts/16115uniquemargins/54ordinaryLeanchunksONEaggregate. ALLlargeralphaexactprefixrepresentedbyalpha=r;FIRSTDmode<=2r. r<=10OLDweight32completeC theoremREUSED/NOTrecounted.',
      formal_scope='ELEVENnewcleanstandardaxiomgenerickernelsincludingFULLresidualnorm/unitboundandboundedTWOcumulativeinduction+ONEnewaggregatecompletefiniteintegercertificate. Actualcomposition/generatingfunction/ratiochain/CassemblyWRITTEN,notendtoendLeancompositions. COMPLETEfinitepremiseis98hosts,notrandomQA.',
      remaining='OriginalgeneralUI/generalC/fullA2OPEN. Mixedbinary/ternaryu>=33actualdiagonalOPEN;theWHOLEextraP_usourcecannotbereplacedbyproperJ_E. Allnewproofskeepfirstphysicalboundary,correctFIRSTmodeguardandordinaryFentry.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',counts=dict(ct),QA=qa['counts'],
      independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,local_files=local,dependency_files=deps,
      sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'pure_ternary_complete_C_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)
if __name__=='__main__':main()
