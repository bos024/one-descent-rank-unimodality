"""Independent full initial atom, signed/clipped coefficients, and actual finite-host control."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from collections import Counter
import sys,json,re,hashlib,time
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE));sys.path.insert(1,str(ROOT))
from verify_tribonacci_quadratic_inverse import (ZERO,ONE,AA,BB,LAM,add,sub,mul,scale,raw,from_lam,into_lam,
    integral,closed,lower_alpha,kernel)
from verify_tribonacci_rich_reverse_quotient import reverse_via_forward,binomial,bernstein_value
from verify_subdegree_CI_entrance import suffix_boxes
def scoped_reports(name,count):
    text=(ROOT/(name+'.log')).read_text(encoding='utf8')
    src=(ROOT/(name+'.lean')).read_text(encoding='utf8')
    assert not any(x in text for x in ['error:','warning:','sorryAx','ofReduceBool','failed']) and 'native_decide' not in src
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
    assert len(rows)==count
    out={}
    for n,raw in rows:
        a=[v.strip() for v in raw.split(',')];assert set(a)<={'propext','Classical.choice','Quot.sound'};out[n]=a
    return out
def head_direct(X,theta,e0,e1):
    w=12+X;r=theta*w;R0=raw(-F(1,4)+e0/2);R1=raw(-F(1,4)+e1/2)
    J=[sub(ONE,R0)];J.append(sub(sub(raw(w),mul(AA,J[0])),R1))
    for n in range(2,5):
        e=sum(binomial(r,k)*binomial(w-k,n-2*k) for k in range(n//2+1))
        J.append(sub(sub(raw(e),mul(AA,J[-1])),mul(BB,J[-2])))
    D=[J[0]]+[sub(J[n],J[n-1]) for n in range(1,5)]
    vals={'D'+str(n)+'_positive':v for n,v in enumerate(D)}
    vals.update({'primitive_minor'+str(n):sub(mul(D[n],D[n]),mul(D[n-1],D[n+1])) for n in range(1,4)})
    return vals
def main():
    started=time.monotonic();ct=Counter();sha=hashlib.sha256()
    data=json.loads((ROOT/'tribonacci_quotient_primitive_certificate_data.json').read_text())
    old=json.loads((SOURCE/'tribonacci_rich_reverse_certificate_data.json').read_text())
    N=data['root_lower_numerator'];M=data['root_denominator'];nA=N-M
    assert N==old['root_lower_numerator'] and M==old['root_denominator']
    produced={(r['u'],r['r']):r for r in data['contexts']};keys={(u,r) for r in range(8,18) for u in range(4,r//2+1)}|{(0,18)}
    assert set(produced)==keys and len(keys)==31;scalars=set()
    for u,r in sorted(keys):
        J,H=reverse_via_forward(closed(u,r));row=produced[u,r]
        assert [into_lam(v) for v in J]==list(map(tuple,row['J']))
        signed=[sub(v,J[n-1] if n else ZERO) for n,v in enumerate(J)];D=[]
        for v in signed:
            if v==ZERO:D.append(ZERO);continue
            if lower_alpha(integral(v),nA,M)>0:D.append(v);a=v
            else:
                a=scale(v,-1);assert lower_alpha(integral(a),nA,M)>0;D.append(ZERO)
            scalars.add(integral(into_lam(a)))
        ms=[sub(mul(D[n],D[n]),mul(D[n-1],D[n+1])) for n in range(1,len(D)-1)]
        assert [into_lam(v) for v in signed]==list(map(tuple,row['signed_primitive']))
        assert [into_lam(v) for v in D]==list(map(tuple,row['positive_primitive']))
        assert [into_lam(v) for v in ms]==list(map(tuple,row['minors']))
        for v in ms:
            if v!=ZERO:
                assert lower_alpha(integral(v),nA,M)>0;scalars.add(integral(into_lam(v)))
        assert D[0]==J[0]
        ct['independent_FULL_initial_atom_primitive_hosts']+=1;ct['independent_signed_and_clipped_coefficients']+=len(D)
        ct['independent_ALL_positive_primitive_LC_minors']+=len(ms)
        sha.update(str((u,r,J,D,ms)).encode())
    for rows in data['complete_head_data'].values():
        for row in rows:
            v=from_lam(row['coefficient'])
            if v!=ZERO:
                assert lower_alpha(integral(v),nA,M)>0;scalars.add(integral(tuple(F(x) for x in row['coefficient'])))
            if row['X_power']==0:assert v!=ZERO
    assert sum(len(v) for v in data['complete_head_data'].values())==235
    bounds=(6,3,2,2)
    for X in map(F,range(7)):
        for theta,e0,e1 in product([F(j,3) for j in range(4)],[F(0),F(1,2),F(1)],[F(0),F(1,2),F(1)]):
            vals=head_direct(X,theta,e0,e1)
            for name,rows in data['complete_head_data'].items():
                v=bernstein_value(rows,X,theta,e0,e1,bounds);assert v==vals[name]
                ct['COMPLETE_tensor_polynomial_identity_reads']+=1
                sha.update(str((X,theta,e0,e1,name,v)).encode())
    # Independent FINITE ACTUAL host; no infinity-padding identification is assumed.
    control=data['actual_residual_primitive_counter'];u=control['u'];r=control['r'];alpha=control['alpha'];n=control['shifted_centre']
    Factual=suffix_boxes(alpha,[2]*u+[3]*r)[:alpha+2*u+3*r+1]
    Dactual=[0,0]+[max(0,Factual[j]-Factual[j-1]) for j in range(2,len(Factual))]
    d=Dactual[2:];ell=d.index(max(d));assert ell==control['shifted_first_D_mode'] and n<ell
    b=[sub(scale(LAM,d[j-1] if j else 0),raw(v)) for j,v in enumerate(d)]
    dp=[sub(v,b[j-1] if j else ZERO) for j,v in enumerate(b)]
    triple=dp[n-1:n+2]
    assert all(lower_alpha(integral(v),nA,M)>0 for v in triple)
    assert [into_lam(v) for v in triple]==list(map(tuple,control['positive_residual_primitive_triple']))
    margin=sub(mul(triple[1],triple[1]),mul(triple[0],triple[2]))
    assert into_lam(margin)==tuple(control['negative_minor'])
    assert lower_alpha(integral(scale(margin,-1)),nA,M)>0
    scalars.add(integral(into_lam(scale(margin,-1))))
    ct['independent_ACTUAL_finite_host_negative_controls']=1
    sha.update(str((alpha,u,r,n,ell,margin)).encode())
    assert sorted(scalars)==list(map(tuple,data['positive_field_triples']))
    source=(ROOT/'TribonacciQuotientPrimitiveCertificate.lean').read_text(encoding='utf8')
    triples=[tuple(map(int,v)) for v in re.findall(r'^  \((-?\d+), (-?\d+), (-?\d+)\)',source,re.M)]
    assert triples==sorted(scalars) and len(triples)==1693
    kernels={name:scoped_reports(name,c) for name,c in [('TribonacciQuotientPrimitiveTransfer',3),('TribonacciQuotientPrimitiveCertificate',1)]}
    qa_data=json.loads((ROOT/'audit_tribonacci_quotient_primitive.json').read_text())
    assert qa_data['status']=='EXACT_QA_PASS_FULL_TRIBONACCI_QUOTIENT_POSITIVE_PRIMITIVE_UNDER_PROOF_AUDIT'
    local=['tribonacci_quotient_positive_primitive_proof.tex','TribonacciQuotientPrimitiveTransfer.lean','TribonacciQuotientPrimitiveTransfer.log',
      'TribonacciQuotientPrimitiveCertificate.lean','TribonacciQuotientPrimitiveCertificate.log',
      'build_tribonacci_quotient_primitive_certificate.py','tribonacci_quotient_primitive_certificate_data.json',
      'audit_tribonacci_quotient_primitive.py','audit_tribonacci_quotient_primitive.json','verify_tribonacci_quotient_primitive.py',
      'probe_tribonacci_quotient_primitive_head.py','probe_tribonacci_quotient_primitive_head.json']
    deps=['tribonacci_rich_reverse_quotient_verification.json','tribonacci_rich_reverse_certificate_data.json',
      'lc_positive_primitive_window_closure_verification.json','lc_positive_primitive_window_closure.tex',
      'LowerFrechetLC.lean','LowerFrechetLC.log','verify_tribonacci_quadratic_inverse.py',
      'verify_tribonacci_rich_reverse_quotient.py','verify_subdegree_CI_entrance.py',
      'build_tribonacci_rich_reverse_certificate.py','probe_tribonacci_quadratic_inverse.py',
      'probe_tribonacci_inverse_bernstein_corners.py','probe_reverse_tribonacci_bernstein_corners.py']
    out=dict(status='PASS_FULL_TERNARY_RICH_QUOTIENT_POSITIVE_PRIMITIVE_LC',new_scoped_reports=4,kernels=kernels,
      theorem='ALLu>=4/r>=2u TRUEpropertribonacciJ hasFULLpositiveprimitive(DeltaJ)^+GLOBALLYLC INCLUDINGd0=J0. SameENTIREr>=18smallnormcone. Strongerthanonlycentres>=2;fullinitial-atomwindowclosurehypothesissatisfied.',
      complete_corrections='BinaryJnew=[2]J+lambdaR1. TernaryJnew=[3]J+lambda(R0+R1-a*lambdaR1)+lambdaR1z. FULLpolynomialidentities/remainderskernelchecked. Signedprimitiveunchangedafterindices1/2respectively,soALLLCcentres>=4inheritregisterednonsymmetricwindowclosure;ALLTHREEheadcentres1/2/3paidexplicitly.',
      head='ALLREALw>=12,r∈[0,w],targetREMAINDERquarterbox:actuald0..d4STRICTLYpositiveandprimitiveLCcentres1/2/3STRICTLYpaid. COMPLETE235Bernsteincoeffs/COMPLETE2016tensoridentitygridreadsbydegreebound(6,3,2,2). No hiddenheadatom/clippingsignorcentre2/3omission.',
      entrance='COMPLETE31FULLprimitivecontexts(ONEpure18+30smallrrich),995signed/clippedreads/933LCminors,includingd0andfirstminor. ALLnonzeroSIGNEDprimitivechoicesseparatelyfield-sign-certified;zeroLCminorsexact. 1693positivefieldtriples/18ordinaryLeanIntegerchunksONEaggregate,includingONEnegativeactualcontrol.',
      actual_obstruction='WHOLEACTUALlambda-residualpositiveprimitiveLCisFALSEonfinitehost1^160 2^20 3^40 atSHIFTEDcentre77<firstDmode107. ExactnegativefieldminorandpositiveinputsCERTIFIED;independentPOSITIVE-SUFFIXBOXfullfinitehostrebuild. ThisisNOTaUI/C/Jprimitivecounter. DoNOTidentifyactualresidualwithproperJ.',
      formal_scope='FOURNEWreports:2COMPLETECommRingquotientcorrectionidentities+ENTIREnatural-index3head/tailjoin+ONEaggregatefieldcertificate. OlduniformLC+FULLprimitivewindowclosure/norm/root/BernsteinkernelsREUSED/NOTrecounted. Coefficient/actualgeneration/LC-window/completeinterpolationandunboundednormconeinductionarewrittenassemblies,notendtoendLeancompositions. Complete31primitiveentranceisNEWexplicitfinitepremise,notoldordinaryJcertificateorQA.',
      remaining='ActualsourceV=S3r(z+S2u+z³B2u),finitepaddingrelativeLC/strongDdiagonalu>=33/generalearlierC/fullA2/ORIGINALUIOPEN. ActualfullC4<=u<=32scopeunchanged. Wholeactuallambda-residualprimitiveFALSE;quotientprimitiveNOWPROVED.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',quotient_primitive_LC='PROVED',counts=dict(ct),QA=qa_data['counts'],
      independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-started,local_files=local,dependency_files=deps,
      sha256={f:hashlib.sha256(((ROOT if f in local else SOURCE)/f).read_bytes()).hexdigest() for f in local+deps})
    (ROOT/'tribonacci_quotient_primitive_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)
if __name__=='__main__':main()
