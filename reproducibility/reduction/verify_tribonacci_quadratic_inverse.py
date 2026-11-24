"""Independent Q(a), closed products, and COMPLETE tensor interpolation checks."""
from pathlib import Path
from fractions import Fraction as F
from math import comb,lcm
from itertools import product
from collections import Counter
import json,re,hashlib,time
ROOT=Path(__file__).resolve().parent
ZERO=(F(0),)*3;ONE=(F(1),F(0),F(0));AA=(F(0),F(1),F(0));LAM=(F(1),F(1),F(0));BB=(F(-1),F(1),F(1))
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def scale(a,s):return tuple(s*x for x in a)
def mul(a,b):
    p=[F(0)]*5
    for i,x in enumerate(a):
        for j,y in enumerate(b):p[i+j]+=x*y
    return(p[0]+2*p[3]-4*p[4],p[1]+2*p[4],p[2]-2*p[3]+4*p[4])
def raw(q):return(F(q),F(0),F(0))
def from_lam(v):
    A,B,C=map(F,v);return(A+B+C,B+2*C,C)
def into_lam(v):
    A,B,C=v;return(A-B+C,B-2*C,C)
def integral(v):
    d=lcm(*(x.denominator for x in v));return tuple(int(d*x) for x in v)
def tri(r,j):return sum(comb(r,k)*comb(r-k,j-2*k) for k in range(max(0,j-r),j//2+1))
def closed(u,r):
    P=[tri(r,j) for j in range(2*r+1)]
    return [sum(comb(u,j)*P[n-j] for j in range(max(0,n-2*r),min(n,u)+1)) for n in range(u+2*r+1)]
def inverse(E):
    f=[]
    for n,e in enumerate(E):
        x=raw(e)
        if n:x=sub(x,mul(AA,f[-1]))
        if n>=2:x=sub(x,mul(BB,f[-2]))
        f.append(x)
    return f
def lower_alpha(v,N,M):
    A,B,C=v
    return A*M*M+B*(N if B>=0 else N+1)*M+C*(N*N if C>=0 else (N+1)**2)
def kernel(name,count):
    log=(ROOT/(name+'.log')).read_text(encoding='utf8');src=(ROOT/(name+'.lean')).read_text(encoding='utf8')
    assert not any(v in log for v in ['error:','warning:','sorryAx','ofReduceBool','failed'])
    assert 'native_decide' not in src
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
    free=re.findall(r"'([^']+)' does not depend on any axioms",log)
    assert len(rows)+len(free)==count
    out={n:[] for n in free}
    for n,txt in rows:
        axioms=[x.strip() for x in txt.split(',')];assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
        out[n]=axioms
    return out
def direct_corners(X,theta,eta0,eta1):
    w=18+X;r=theta*w;x0=raw(-F(1,4)+eta0/2);x1=raw(-F(1,4)+eta1/2)
    x2=mul(LAM,sub(sub(ONE,mul(AA,x1)),x0))
    x3=mul(LAM,sub(sub(raw(w),mul(AA,x2)),x1))
    x4=mul(LAM,sub(sub(raw(w*(w-1)/2+r),mul(AA,x3)),x2))
    x5=mul(LAM,sub(sub(raw(w*(w-1)*(w-2)/6+r*(w-1)),mul(AA,x4)),x3))
    def sq(v):return mul(v,v)
    s12=add(x1,x2);s23=add(x2,x3);s34=add(x3,x4)
    t123=add(s12,x3);t234=add(s23,x4)
    return {'binary_last_minor':sub(sq(s23),mul(s12,s34)),
      'ternary_penultimate_minor':sub(sq(t234),mul(t123,add(s34,x5))),
      'ternary_last_minor':sub(sq(t123),mul(add(x0,s12),t234)),
      'binary_last_value':s12,'ternary_penultimate_value':t123,'ternary_last_value':add(x0,s12)}
def basis_value(k,d,t):return F(comb(d,k))*t**k*(1-t)**(d-k)
def corner_value(rows,X,theta,e0,e1):
    grouped={}
    for row in rows:grouped.setdefault(row['X_power'],[]).append(row)
    out=ZERO
    for n,rs in grouped.items():
        degree=tuple(max(row['box_index'][j] for row in rs) for j in range(3))
        assert n<=4 and all(v<=2 for v in degree)
        assert {tuple(row['box_index']) for row in rs}==set(product(*(range(d+1) for d in degree)))
        for row in rs:
            s=X**n
            for k,d,t in zip(row['box_index'],degree,[theta,e0,e1]):s*=basis_value(k,d,t)
            out=add(out,scale(from_lam(row['coefficient']),s))
    return out
def main():
    start=time.monotonic();ct=Counter();sha=hashlib.sha256()
    data=json.loads((ROOT/'tribonacci_inverse_complete_certificate_data.json').read_text())
    N=data['root_lower_numerator'];M=data['root_denominator'];nA=N-M
    def pl(v):return v**3-v*v*M-v*M*M-M**3
    assert pl(N)<0<pl(N+1)
    assert nA**3+2*nA*nA*M-2*M**3<0<(nA+1)**3+2*(nA+1)**2*M-2*M**3
    assert F(83,100)<=F(nA,M)<F(nA+1,M)<=F(84,100)
    produced={(row['u'],row['r']):row for row in data['complete_contexts']};keys=set();scalars=set()
    for u in range(19):
        for r in range(19-u):
            if not 1<=u+r<=18 or (u,r)==(0,2):continue
            keys.add((u,r));E=closed(u,r);f=inverse(E);p=f[:-2]
            ms=[sub(mul(p[n],p[n]),mul(p[n-1],p[n+1])) for n in range(1,len(p)-1)]
            row=produced[u,r]
            assert E==row['E'] and [into_lam(v) for v in p]==list(map(tuple,row['prefix']))
            assert [into_lam(v) for v in ms]==list(map(tuple,row['minors']))
            for v in p+ms:
                assert v!=ZERO and lower_alpha(integral(v),nA,M)>0
                scalars.add(integral(into_lam(v)))
            ct['independent_complete_base_hosts']+=1;ct['independent_retained_base_coefficients']+=len(p);ct['independent_base_LC_minors']+=len(ms)
            sha.update(str((u,r,E,p,ms)).encode())
    assert keys==set(produced) and len(keys)==188
    bad=inverse(closed(0,2))[:-2];exception=sub(mul(bad[1],bad[1]),mul(bad[0],bad[2]))
    assert exception==(0,-1,1) and into_lam(exception)==(2,-3,1)
    corners=data['complete_corner_data'];assert sum(len(v) for v in corners.values())==125
    for name,rows in corners.items():
        for row in rows:
            v=from_lam(row['coefficient'])
            if v!=ZERO:
                assert lower_alpha(integral(v),nA,M)>0
                scalars.add(integral(tuple(F(x) for x in row['coefficient'])))
            if row['X_power']==0:assert v!=ZERO and lower_alpha(integral(v),nA,M)>0
    # COMPLETE tensor interpolation: degrees <=(4,2,2,2), not random point sampling.
    for X in map(F,range(5)):
        for theta,e0,e1 in product([F(0),F(1,2),F(1)],repeat=3):
            direct=direct_corners(X,theta,e0,e1)
            for name,rows in corners.items():
                expected=corner_value(rows,X,theta,e0,e1)
                assert direct[name]==expected,(X,theta,e0,e1,name)
                ct['COMPLETE_tensor_polynomial_identity_reads']+=1
                sha.update(str((X,theta,e0,e1,name,expected)).encode())
    assert sorted(scalars)==list(map(tuple,data['positive_field_triples']))
    source=(ROOT/'TribonacciInverseCompleteCertificate.lean').read_text(encoding='utf8')
    triples=[tuple(map(int,v)) for v in re.findall(r'^  \((-?\d+), (-?\d+), (-?\d+)\)',source,re.M)]
    assert triples==sorted(scalars) and len(triples)==len(set(triples))
    for v in triples:
        assert lower_alpha(integral(from_lam(v)),nA,M)>0
    qa_data=json.loads((ROOT/'audit_tribonacci_quadratic_inverse.json').read_text())
    assert qa_data['status']=='EXACT_QA_PASS_FULL_COUNT_TRIBONACCI_QUADRATIC_INVERSE_UNDER_PROOF_AUDIT'
    kernels={n:kernel(n,c) for n,c in [('TribonacciInverseTerminalNorm',6),('TribonacciInverseClosure',5),('TribonacciInverseCompleteCertificate',2)]}
    files=['tribonacci_quadratic_inverse_proof.tex','TribonacciInverseTerminalNorm.lean','TribonacciInverseTerminalNorm.log',
      'TribonacciInverseClosure.lean','TribonacciInverseClosure.log','TribonacciInverseCompleteCertificate.lean',
      'TribonacciInverseCompleteCertificate.log','build_tribonacci_inverse_complete_certificate.py',
      'tribonacci_inverse_complete_certificate_data.json','audit_tribonacci_quadratic_inverse.py',
      'audit_tribonacci_quadratic_inverse.json','verify_tribonacci_quadratic_inverse.py',
      'probe_tribonacci_quadratic_inverse.py','probe_tribonacci_inverse_bernstein_corners.py',
      'probe_tribonacci_inverse_bernstein_corners.json']
    out=dict(status='PASS_FULL_COUNT_TRIBONACCI_QUADRATIC_INVERSE_PREFIX',new_scoped_reports=13,kernels=kernels,
      theorem='ALLu/r>=0,w>=1,D=u+2r>=2:ZERO-TRUNCATEDfiniteprefixof[2]^u[3]^r/(1+a*z+b*z²)throughD-2isSTRICTLYpositive/GLOBALLYLC EXCEPTONLY(u0,r2). lambdaTRIBONACCIroot,a=lambda-1,b=1/lambda. AllcountsUNBOUNDED. LastTWOcoefficientsdiscarded/maybeNEGATIVE. D1prefixEMPTY.',
      norm='EXACT ALLcountsterminalQ(e0,e1)=e0²+a*e0e1+b*e1²=(a²)^u*(1-a)^r. BinarypairlineartransformscalesQbya²;ternaryscalesby1-a. COMPLETEtwo-Natinduction. BOTHnonreal-rootphaseretained. CoercivityQ>=(e0²+e1²)/10;w>=18impliesFULLquarterbox. NOphaseerasure.',
      unbounded_corners='ONEbinarynewvalue/oneuncoveredminor;TWOternarynewvalues/TWOuncoveredminors. ALLSIXrawcornerexpressionsPOSITIVEforALLREALw>=18,0<=r<=w,terminalquarterbox. COMPLETE125Q(lambda)Bernsteincoefficientsnonnegative/ALLX0positive. IndepCOMPLETE810tensoridentitygridreadsforDEGREEBOUND(4,2,2,2)proveENTIREpolynomialidentities,NOTcountboundedparameterQA. Rootintervalwidth10^-50signedbyEXACTintegercubics;allfieldboundsLean-certified.',
      entrance='COMPLETE188contexts1<=u+r<=18EXCEPTu0r2;3228retainedcoeffs+2856LCminorsALLpositive. D1emptycontextexplicit. IndependentCLOSEDbinomial/trinomialcoefficients/FORWARDinverseinDIFFERENTQ(a)basis/ALLcontextbytesmatch. ONEsingleexcludedprefix(1,2-a,4-3a)minor=a²-a<0. StronginductionALLhighercountsformalizedaswholepredicatekernel.',
      formal_scope='THIRTEENNEWreports:6terminalnorm/coercivity/box+5root/interval/Bernsteinsum/ALLcountpredicate/exception+2COMPLETEfinitefield/root certificates. 61ordinaryLeanIntegerchunksONEaggregate;noNative/sorry/nonstandardaxioms. Seq-to-pair/coefficient/convolution/actualrootlifting/COMPLETEboundeddegreeinterpolationassemblyandwholeprefixinductionarewrittenproof;NOendtoendLeancompositions. CompletefiniteentranceisEXPLICIT,notrandomQA.',
      remaining='TRIBONACCIkerneltheoremONLY. ActualfullDtransferstillOPEN. OppositeREVERSEDquadraticquotienthasDIFFERENTdenominator;doNOTsilentlyidentify. Actualunboundeddiagonalu>=33/generalearlierC/fullA2/ORIGINALundilatedcoefficientUIOPEN. NoactualfullC32rangeenlargementalone.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',counts=dict(ct),QA=qa_data['counts'],
      positive_field_triples=len(triples),kernel_chunks=data['chunks'],Bernstein_coefficients=125,
      independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
      sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'tribonacci_quadratic_inverse_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)
if __name__=='__main__':main()
