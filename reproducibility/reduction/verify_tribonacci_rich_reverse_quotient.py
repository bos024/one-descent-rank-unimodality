"""Independent forward reversed denominator and COMPLETE 3105 interpolation reads."""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
from itertools import product
from collections import Counter
import sys,json,re,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT));sys.path.insert(1,str(SOURCE))
from verify_tribonacci_quadratic_inverse import (ZERO,ONE,AA,BB,LAM,add,sub,scale,mul,raw,from_lam,into_lam,
    integral,closed,lower_alpha,kernel,corner_value)
def pwr(v,n):
    out=ONE
    for j in range(n):out=mul(out,v)
    return out
def reverse_via_forward(E):
    alpha=mul(LAM,AA);H=[]
    for n,e in enumerate(E):
        v=raw(e)
        if n:v=sub(v,mul(alpha,H[-1]))
        if n>=2:v=sub(v,mul(LAM,H[-2]))
        H.append(v)
    return list(reversed([mul(LAM,v) for v in H[:-2]])),H
def binomial(q,k):
    v=F(1,factorial(k))
    for j in range(k):v*=q-j
    return v
def reverse_direct(X,theta,e0,e1):
    w=18+X;r=theta*w;x=[raw(-F(1,4)+e0/2),raw(-F(1,4)+e1/2)]
    for k in range(2,8):
        t=k-2;head=sum(binomial(r,j)*binomial(w-j,t-2*j) for j in range(t//2+1))
        x.append(sub(sub(scale(BB,head),mul(AA,x[-1])),mul(BB,x[-2])))
    def s(*inds):
        out=ZERO
        for i in inds:out=add(out,x[i])
        return out
    def sq(v):return mul(v,v)
    return {'binary_last_minor':sub(sq(s(4,5)),mul(s(3,4),s(5,6))),
      'ternary_penultimate_minor':sub(sq(s(4,5,6)),mul(s(3,4,5),s(5,6,7))),
      'ternary_last_minor':sub(sq(s(3,4,5)),mul(s(2,3,4),s(4,5,6))),
      'binary_last_value':s(3,4),'ternary_penultimate_value':s(3,4,5),'ternary_last_value':s(2,3,4)}
def head_direct(X,theta,e0,e1):
    w=12+X;r=theta*w;R0=raw(-F(1,4)+e0/2);R1=raw(-F(1,4)+e1/2)
    J0=sub(ONE,R0);J1=sub(sub(raw(w),mul(AA,J0)),R1)
    J2=sub(sub(raw(w*(w-1)/2+r),mul(AA,J1)),mul(BB,J0))
    J3=sub(sub(raw(w*(w-1)*(w-2)/6+r*(w-1)),mul(AA,J2)),mul(BB,J1))
    return {'J0_positive':J0,'J1_positive':J1,'J2_positive':J2,
      'first_LC_minor':sub(mul(J1,J1),mul(J0,J2)),
      'second_LC_minor':sub(mul(J2,J2),mul(J1,J3))}
def bernstein_value(rows,X,theta,e0,e1,bounds):
    grouped={}
    for row in rows:grouped.setdefault(row['X_power'],[]).append(row)
    total=ZERO
    for n,rs in grouped.items():
        deg=tuple(max(row['box_index'][j] for row in rs) for j in range(3))
        assert n<=bounds[0] and all(d<=b for d,b in zip(deg,bounds[1:]))
        assert set(tuple(row['box_index']) for row in rs)==set(product(*(range(d+1) for d in deg)))
        from math import comb
        for row in rs:
            weight=X**n
            for k,d,t in zip(row['box_index'],deg,[theta,e0,e1]):weight*=comb(d,k)*t**k*(1-t)**(d-k)
            total=add(total,scale(from_lam(row['coefficient']),weight))
    return total
def main():
    start=time.monotonic();ct=Counter();sha=hashlib.sha256()
    data=json.loads((ROOT/'tribonacci_rich_reverse_certificate_data.json').read_text())
    N=data['root_lower_numerator'];M=data['root_denominator'];nA=N-M
    old=json.loads((SOURCE/'tribonacci_inverse_complete_certificate_data.json').read_text())
    assert N==old['root_lower_numerator'] and M==old['root_denominator']
    produced={(r['u'],r['r']):r for r in data['contexts']};keys={(u,r) for r in range(8,18) for u in range(4,r//2+1)}|{(0,18)}
    assert set(produced)==keys and len(keys)==31
    scalars=set();S=mul(LAM,mul(AA,AA))
    for u,r in sorted(keys):
        row=produced[u,r];E=closed(u,r);J,H=reverse_via_forward(E)
        assert E==row['E'] and [into_lam(v) for v in J]==list(map(tuple,row['J']))
        startidx=2 if u==0 else 0;assert row['retained_start']==startidx;P=J[startidx:]
        ms=[sub(mul(P[n],P[n]),mul(P[n-1],P[n+1])) for n in range(1,len(P)-1)]
        assert [into_lam(v) for v in P]==list(map(tuple,row['retained_coefficients']))
        assert [into_lam(v) for v in ms]==list(map(tuple,row['minors']))
        for v in P+ms:
            assert lower_alpha(integral(v),nA,M)>0
            scalars.add(integral(into_lam(v)))
        R0=sub(ONE,J[0]);R1=sub(sub(raw(u+r),mul(AA,J[0])),J[1])
        remnorm=add(sub(mul(BB,mul(R0,R0)),mul(AA,mul(R0,R1))),mul(R1,R1))
        termnorm=add(add(mul(BB,mul(H[-1],H[-1])),mul(AA,mul(H[-1],H[-2]))),mul(H[-2],H[-2]))
        expected=mul(pwr(S,u),pwr(BB,r+1));assert remnorm==termnorm==expected
        for n,e in enumerate(E):
            v=J[n] if n<len(J) else ZERO
            if 0<=n-1<len(J):v=add(v,mul(AA,J[n-1]))
            if 0<=n-2<len(J):v=add(v,mul(BB,J[n-2]))
            if n==0:v=add(v,R0)
            if n==1:v=add(v,R1)
            assert v==raw(e)
            ct['independent_ALL_division_identity_reads']+=1
        ct['independent_complete_entrance_hosts']+=1
        ct['independent_base_coefficients']+=len(P);ct['independent_base_LC_minors']+=len(ms)
        ct['independent_full_two_phase_norm_identities']+=1
        sha.update(str((u,r,J,remnorm)).encode())
    controls={
      'b_minus_half':sub(BB,raw(F(1,2))),
      'three_quarters_minus_a_square':sub(raw(F(3,4)),mul(AA,AA)),
      'three_fifths_minus_b':sub(raw(F(3,5)),BB),
      'two_fifths_minus_a_square_b':sub(raw(F(2,5)),mul(mul(AA,AA),BB)),
      'sigma_minus_one':sub(S,ONE),'one_minus_b':sub(ONE,BB),
      'pure_eighteen_norm_budget':sub(raw(F(1,64)),pwr(BB,19)),
      'b_positive':BB,'a_square_b_positive':mul(mul(AA,AA),BB)}
    for k,v in controls.items():
        assert from_lam(data['root_obligations'][k])==v and lower_alpha(integral(v),nA,M)>0
        scalars.add(integral(into_lam(v)))
    count=0
    for kind,polys in data['complete_corner_data'].items():
        for name,rows in polys.items():
            count+=len(rows)
            for row in rows:
                v=from_lam(row['coefficient'])
                if v!=ZERO:
                    assert lower_alpha(integral(v),nA,M)>0
                    scalars.add(integral(tuple(F(x) for x in row['coefficient'])))
                if row['X_power']==0:assert v!=ZERO
    assert count==478
    # COMPLETE interpolation grids, with proven formula degrees(8,4,2,2)/(4,2,2,2).
    for kind,direct,bounds in [('reverse_extension',reverse_direct,(8,4,2,2)),('whole_J_head',head_direct,(4,2,2,2))]:
        polys=data['complete_corner_data'][kind]
        for X in map(F,range(bounds[0]+1)):
            for theta,e0,e1 in product([F(j,bounds[1]) for j in range(bounds[1]+1)],[F(0),F(1,2),F(1)],[F(0),F(1,2),F(1)]):
                vals=direct(X,theta,e0,e1)
                for name,rows in polys.items():
                    v=bernstein_value(rows,X,theta,e0,e1,bounds);assert v==vals[name],(kind,name,X,theta,e0,e1)
                    ct['COMPLETE_tensor_identity_reads_'+kind]+=1
                    sha.update(str((kind,name,X,theta,e0,e1,v)).encode())
    assert sorted(scalars)==list(map(tuple,data['positive_field_triples']))
    source=(ROOT/'TribonacciRichReverseCertificate.lean').read_text(encoding='utf8')
    triples=[tuple(map(int,v)) for v in re.findall(r'^  \((-?\d+), (-?\d+), (-?\d+)\)',source,re.M)]
    assert triples==sorted(scalars) and len(triples)==2350
    kernels={n:kernel(n,c) for n,c in [('TribonacciRichReverseQuotient',6),('TribonacciRichReverseCertificate',1)]}
    qa_data=json.loads((ROOT/'audit_tribonacci_rich_reverse_quotient.json').read_text())
    assert qa_data['status']=='EXACT_QA_PASS_PROPER_TRIBONACCI_RICH_QUOTIENT_UNDER_PROOF_AUDIT'
    local=['tribonacci_rich_reverse_quotient_proof.tex','TribonacciRichReverseQuotient.lean','TribonacciRichReverseQuotient.log',
      'TribonacciRichReverseCertificate.lean','TribonacciRichReverseCertificate.log','build_tribonacci_rich_reverse_certificate.py',
      'tribonacci_rich_reverse_certificate_data.json','audit_tribonacci_rich_reverse_quotient.py','audit_tribonacci_rich_reverse_quotient.json',
      'verify_tribonacci_rich_reverse_quotient.py','probe_reverse_tribonacci_bernstein_corners.py',
      'probe_reverse_tribonacci_bernstein_corners.json','probe_reverse_tribonacci_head_payments.py','probe_reverse_tribonacci_head_payments.json']
    deps=['tribonacci_quadratic_inverse_verification.json','tribonacci_inverse_complete_certificate_data.json',
      'verify_tribonacci_quadratic_inverse.py','probe_tribonacci_quadratic_inverse.py','probe_tribonacci_inverse_bernstein_corners.py',
      'TribonacciInverseClosure.lean','TribonacciInverseClosure.log']
    out=dict(status='PASS_UNBOUNDED_TERNARY_RICH_PROPER_QUADRATIC_QUOTIENT',new_scoped_reports=7,kernels=kernels,
      theorem='ALLu>=4,r>=2u:TRUEpolynomialdivision[2]^u[3]^r=(1+a*z+b*z²)J+R0+R1z hasSTRICTLYpositive/GLOBALLYordinaryLC J. NOupperbinary/threecountbound. ActualD/primitiveLCnotasserted.',
      norm_cone='MOREGENERALALLr>=18,u>=0withb*sigma^u*b^r<=1/64 havepositiveGLOBALordinaryLCJ; sigma=a²/b=1+2lambda-lambda²>1. FirstprovepureALLr>=18fromONEpure18seedandcontractingternarynorm;thenALLbinarycountsbyINCREASINGnormtargetinductionsinceEVERYearliernorm<=target. No unboundedcriticaldiagonalpremise.',
      norm='BOTHreverse-normalizedinverseTERMINALpairANDsignedPOLYNOMIALREMAINDERpairhaveR=b*x²+a*xy+y²=b*sigma^u*b^r. Binarymap/ADJUGATEremainderMAPbothnormscaleSIGMA;ternarymap/dualremainderMAPbothscaleb. EXACTtwo-countnorminduction. StrongcoercivityR>=sumSquares/4;richR=b*(a²*b)^u*b^(r-2u)<=48/3125<1/64ALLu>=4. ALLphases/remaindersretained.',
      full_head='ReverseprefixthroughD-4givesJ[2..]LCONLYcentres>=3. EXPLICITBOTHmissingJcentre1AND2andJ0/J1/J2positivepaidatALLREALw>=12,r∈[0,w],REMAINDERquarterboxby102Bernsteincoeffs. Neveromitcentre2. ReverseextensionALLSIXcornersforw>=18/fullterminalboxpaidby376coeffs. TOTAL478coeffs;COMPLETE3105tensoridentityreadswithdegreebounds(8,4,2,2)/(4,2,2,2),notparameterQA.',
      entrance='ONEpureu0r18J[2..]seed+COMPLETE30richr8..17quotients=31contexts;993coefficients/931minorsallpositive. 2350distinctfieldtriples/25LeanIntegerchunksONEaggregate. IndependentlyclosedCIproducts/FORWARDinverseofREVERSEDdenominatorinQ(a),notprimaryBACKWARDJinQ(lambda). BOTHterminal/remaindernormandALLdivisioncoefficientsindependentlyreconstructed.',
      formal_scope='SEVENnewreports:6completepair/dual-pairnorms/two-Natnorm/strongbox/richall-u-kpayment/increasingbinaryconepredicate+1ALLfinitecertificate. Oldroot/BernsteinsumkernelsREUSEDwithoutrecount. LCconvolution,properdivision/reversal/pairidentifications,completebounded-degreeinterpolationandwholepure-then-binarynormconeassemblyarewrittenproof,NOendtoendLeancompositions. ONEpure+30smallrfiniteentranceEXPLICIT/no sampled universalpremise.',
      remaining='PositiveprimitiveLCofJstillSEPARATEOPENcandidate(despite490hostdiagnostics). ActualinfiniteonesDhasALLotherQ3sourcecomponents;wholeactuallambda-residualordinaryLCisFALSE(u71r209,n400). DoNOTinferactualstrongdiagonal/generalC/fullA2/ORIGINALUIfromquotientalone. ActualcompleteCbinaryrange4..32unchanged.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',primitive_LC='OPEN',counts=dict(ct),QA=qa_data['counts'],
      independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,local_files=local,dependency_files=deps,
      sha256={f:hashlib.sha256(((ROOT if f in local else SOURCE)/f).read_bytes()).hexdigest() for f in local+deps})
    (ROOT/'tribonacci_rich_reverse_quotient_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)
if __name__=='__main__':main()
