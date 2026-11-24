"""Independent closed suffix-box/Fibonacci sums and exact quadratic signs."""
from pathlib import Path
from math import comb
from itertools import accumulate
from random import Random
from collections import Counter
import sys,json,re,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_ternary_forward_inverse import closed,inv,qa,qm,qs,sub,qpow
from verify_subdegree_CI_entrance import suffix_boxes
ZERO=(0,0);ONE=(1,0);Q=(0,1);PHI=(1,1)
def phitoq(v):return(v[0]+v[1],v[1])
def qtoph(v):return(v[0]-v[1],v[1])
def reference_closed(r,N):
    B=[0]*(N+1)
    for j in range(r):
        for i,v in enumerate(closed(0,j)):
            if i+j<=N:B[i+j]+=v
    E=closed(0,r);fib=[sum(comb(n-k,k) for k in range(n//2+1)) for n in range(max(0,N-r)+1)]
    for n in range(r,N+1):B[n]+=sum(E[j]*fib[n-r-j] for j in range(min(2*r,n-r)+1))
    return B
def full_C(F,D,hi,ct,tag):
    G=list(accumulate(F));best=1
    for N in range(4,hi+1):
        k=N-3
        if G[k]*G[best-1]<G[best]*G[k-1]:best=k
        assert G[best]*D[N-1]>=G[best-1]*D[N]
        ct[tag+'_all_shift_prefix_payments']+=1;ct[tag+'_logical_shift_reads']+=N-3
def reports(name,n):
    src=(ROOT/(name+'.lean')).read_text(encoding='utf8');log=(ROOT/(name+'.log')).read_text(encoding='utf8')
    assert not any(v in log for v in ['warning:','error:','sorryAx','ofReduceBool','failed']) and 'native_decide' not in src
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==n;out={}
    for name,raw in rows:
        a=[v.strip() for v in raw.split(',') if v.strip()];assert set(a)<={'propext','Classical.choice','Quot.sound'};out[name]=a
    return out
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256()
    data=json.loads((ROOT/'stationary_ternary_reference_base_data.json').read_text());R=reference_closed(6,18)
    H=[(R[n]- (R[n-1] if n else 0),-(R[n-1] if n else 0)) for n in range(19)]
    assert [qtoph(v) for v in H]==list(map(tuple,data['H']))
    C=[R[n]-(R[n-1] if n else 0)-(R[n-2] if n>1 else 0) for n in range(19)];assert C==data['C']
    assert data['LC_centres']==list(range(9,18));ms=[sub(qm(H[n],H[n]),qm(H[n-1],H[n+1])) for n in range(9,18)]
    assert [qtoph(v) for v in ms]==list(map(tuple,data['LC_minors'])) and [qtoph(v) for v in H[8:]]==list(map(tuple,data['positive_tail_values']))
    vals=H[8:]+ms
    for v in vals:assert qs(v)>0
    src=(ROOT/'StationaryTernaryReferenceBase.lean').read_text(encoding='utf8')
    pairs=[tuple(map(int,v)) for v in re.findall(r'0<\(\((-?\d+):ℝ\)\+\((-?\d+):ℝ\)\*q\)',src)]
    assert pairs==vals and len(vals)==20
    n=618033988749;M=10**12
    assert n*n+n*M-M*M<0<(n+1)*(n+1)+(n+1)*M-M*M
    assert all(a*M+b*(n if b>=0 else n+1)>0 for a,b in vals)
    ct['COMPLETE_independent_fixed_six_H_tail_values']=11;ct['COMPLETE_independent_fixed_six_H_tail_minors']=9
    sha.update(str((C,H,ms)).encode())
    for r in range(6,66):
        R=reference_closed(r,5*r+3);H=[(R[n]-(R[n-1] if n else 0),-(R[n-1] if n else 0)) for n in range(len(R))];tau=qpow(qm((2,0),qm(Q,Q)),r)
        assert H[3*r]==tau and H[3*r+1]==qm((0,-1),tau)
        assert H[3*r-1]==qm(PHI,sub(ONE,tau))
        for n in range(r+3,3*r):
            assert qs(sub(qm(H[n],H[n]),qm(H[n-1],H[n+1])))>=0;ct['independent_reference_H_LC_tail_minors']+=1
        for n in range(r+3,3*r+1):assert R[n]**2>=R[n-1]*R[n+1];ct['independent_reference_ordinary_LC_head_minors']+=1
        assert R[3*r+1]**2<R[3*r]*R[3*r+2];ct['independent_reference_FIRST_late_LC_failure_controls']+=1
        # Old forward-CI corner pays the smaller new H corner, without dropping either tail phase.
        Inew=inv(closed(0,r+1));oldcorner=sub(qm(Inew[-2],Inew[-2]),qm(Inew[-3],Inew[-1]))
        Hcorner=sub(qm(qm(PHI,sub(ONE,tau)),qm(PHI,sub(ONE,tau))),ZERO) # overwritten by full exact triple below
        A=qa(sub(qm(PHI,(r-1,0)),ONE),qm((2,0),tau))
        B=qa(qm(PHI,sub(ONE,tau)),qm(qm(Q,Q),tau));C=qm(qm((2,0),qm(Q,Q)),tau)
        Hcorner=sub(qm(B,B),qm(A,C));assert Hcorner==qa(oldcorner,qm(qm((2,0),Q),tau)) and qs(Hcorner)>=0
        ct['independent_terminal_corner_payments_from_OLD_forward_CI']+=1
        D=[0,0]+[R[n]-R[n-1] for n in range(2,len(R))];assert all(v>=0 for v in D)
        full_C(R,D,5*r,ct,'independent_REFERENCE');ct['independent_closed_reference_hosts']+=1
        sha.update(str((r,R,H[3*r-2:3*r+3],Hcorner)).encode())
    rng=Random(2026110148)
    cases=[(r,u,a) for r in range(6,26) for u in [2*r-3,2*r-2,3*r] for a in [1,2,u+r]]
    cases +=[(r,2*r-3+rng.randint(0,2*r),rng.randint(1,220)) for r in [rng.randint(6,75) for _ in range(150)]]
    for r,u,alpha in cases:
        F=suffix_boxes(alpha,[2]*u+[3]*r);D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];L=D.index(max(D));W=3*r;N0=u+r+2
        R=reference_closed(r,N0)
        assert F[:N0]==R[:N0] and R[N0]-F[N0]==(2 if alpha==1 else 1)
        ct['independent_exact_ACTUAL_FIRSTbinary_loss_and_prefix_controls']+=1
        full_C(F,D,L,ct,'independent_ACTUAL_dense');ct['independent_positive_suffix_box_dense_hosts']+=1
        sha.update(str((r,u,alpha,F,D,L,N0)).encode())
    qa_data=json.loads((ROOT/'audit_stationary_ternary_reference_C.json').read_text());assert qa_data['status']=='EXACT_QA_PASS_ALL_STATIONARY_THREE_REFERENCE_AND_BINARY_DENSE_ACTUAL_C_UNDER_PROOF_AUDIT'
    local=['stationary_ternary_reference_and_binary_dense_C_proof.tex','StationaryTernaryReferenceC.lean','StationaryTernaryReferenceC.log',
      'StationaryTernaryReferenceBase.lean','StationaryTernaryReferenceBase.log','build_stationary_ternary_reference_base.py',
      'stationary_ternary_reference_base_data.json','audit_stationary_ternary_reference_C.py','audit_stationary_ternary_reference_C.json',
      'verify_stationary_ternary_reference_C.py']
    deps=['ternary_forward_inverse_verification.json','ternary_forward_inverse_clean_log_verification.json',
      'ternary_forward_inverse_and_diagonal_companion.tex','ordinary_tail_to_complete_C_verification.json','OrdinaryTailToCompleteC.lean','OrdinaryTailToCompleteC.log',
      'pure_ternary_complete_C_verification.json','first_missing_renewal_envelope.tex',
      'reference_ordinary_golden_prefix_verification.json','previous_boundary_C_verification.json','previous_boundary_C_proof.tex',
      'universal_physical_boundary_C_verification.json','multitail_binary_prefix_finite_principle_verification.json',
      'RenewalRootPrimitiveCut.lean','RenewalRootPrimitiveCut.log','TernaryRichCompleteC.lean','TernaryRichCompleteC.log',
      'verify_ternary_forward_inverse.py','verify_subdegree_CI_entrance.py']
    out=dict(status='PASS_ALL_STATIONARY_THREE_REFERENCE_AND_BINARY_DENSE_ACTUAL_COMPLETE_C',new_scoped_reports=5,
      kernels={'StationaryTernaryReferenceC':reports('StationaryTernaryReferenceC',4),'StationaryTernaryReferenceBase':reports('StationaryTernaryReferenceBase',1)},
      reference='EVERYr>=0:infiniteBINARYreferenceR=B3r+S3r*H2 hasFULLC EVERYcurrent/EVERYshift>=3,THREEcountUNBOUNDED. r<=5OLDweight32actualfiniteprefixlimit;ALLr>=6NEWresidualtailinduction+ordinaryentry+OLDlateReferenceC.',
      residual='ALLr>=6:H=R-phi*zR hasSTRICTLYpositiveH2..H_W andLCatEVERYr+3<=n<W=3r. ALTERNATINGtailH_(W+j)=(-q)^j*tauKEPT,tau=(2q²)^r. CompleteprefixHtailONLY,notfullalternatingFPSLC.',
      reference_ordinary='ALLr>=6:ordinaryREFERENCEF LC EVERYcentre r+3<=n<=W. FIRSTlatecentreW+1STRICTLYNEGATIVEforALLr>=1. ReferenceordinaryLCNOTclaimedbeyondW;referenceFULLCindependentlyinheritsOLDlateCfromW-1.',
      actual='EVERYACTUAL1alpha2u3r,ALLalpha>=1,r>=0,u>=max(0,2r-3):FULLC EVERYcurrent/EVERYshift>=3. BOTHbinaryandternarycountsUNBOUNDED. Atu=2r-3firstbinarylossEXACTLYW-1lowersonlycurrentD;earlierprefixreference. AllN>=WOLDuniversalACTUALC. r<=5OLDweight32/purebinary.',
      heredity='EntireHLCr-append:unperturbedKcontrols|M_K|<=Kprev/K<=2KprevALLn>=6;TWOnewleftentriespaidbylosses1,r+2-phi,(r²+5r+10)/2-phi(r+2),c-4b-1=r(r-7)/2+(2-phi)(r-2)>=0. MiddleLC3windowfromtruncatedpositiveoldtail;penultimatenextlowered;oneNEWterminalminor=OLDpureforwardCIcorner+2q*tau>=0.',
      entrance='ONEcompletefixedr6base:11positiveH8..H18+9positiveLCminorscentres9..17. TWOindependentrebuilds:C/(1+qz)forwardvsCLOSEDpositiveB3r+S3rH2/Fibonacci-binomialsum. ALL20scalarswithinternallyPROVEDexactquadraticrootintervalkernelcheckedinONEaggregate;NOnewactualhostfiniteentrance.',
      formal_scope='FOURnewcleanstandardaxiomgenericreports(fullunperturbedKrecurrence/minormajorant,completeTWOleftpayments,oldCIterminalbudgetinheritance,two-endedNatreadguards)+ONEfixedbaseaggregate. Genericthirdrecurrencehelpersreused/copied,notseparatelyrecounted. Wholecoefficient/reference/actualassemblyWRITTEN,notendtoendLeancompositions.',
      remaining='OriginalgeneralUI/generalC/fullA2OPEN. Richr>=2u/u>=33criticalordinarydiagonalSTILLOPEN. NewACTUALbinarydenseconeisu>=2r-3,notallmixed2/3profiles. Finiteordinaryactual/reference-relativeLCdiagnosticremainsUNPROVED.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',counts=dict(ct),QA=qa_data['counts'],independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      local_files=local,dependency_files=deps,sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'stationary_ternary_reference_C_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)
if __name__=='__main__':main()
