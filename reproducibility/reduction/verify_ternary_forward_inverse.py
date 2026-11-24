"""Independent binomial/trinomial expansion and alternating exact inverse."""
from pathlib import Path
from math import comb,factorial
from random import Random
from collections import Counter
import sys,json,re,hashlib,time
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes

def qa(a,b):return(a[0]+b[0],a[1]+b[1])
def qm(a,b):return(a[0]*b[0]+a[1]*b[1],a[0]*b[1]+a[1]*b[0]-a[1]*b[1])
def qs(a):
    A=2*a[0]-a[1];B=a[1]
    if A>=0 and B>=0:return int(A+B>0)
    if A<=0 and B<=0:return -int(A+B<0)
    s=(A*A>5*B*B)-(A*A<5*B*B)
    return s if A>0 else -s
def sub(a,b):return(a[0]-b[0],a[1]-b[1])
def qpow(a,n):
    out=(1,0)
    for _ in range(n):out=qm(out,a)
    return out
def tri(r,j):
    return sum(comb(r,k)*comb(r-k,j-2*k) for k in range(max(0,j-r),j//2+1))
def closed(u,r):
    T=[tri(r,j) for j in range(2*r+1)]
    return [sum(comb(u,k)*T[n-k] for k in range(max(0,n-2*r),min(u,n)+1)) for n in range(u+2*r+1)]
def inv(E):
    powers=[qpow((0,-1),j) for j in range(len(E))]
    return [tuple(sum(E[n-j]*powers[j][k] for j in range(n+1)) for k in range(2)) for n in range(len(E))]
def lc(a,n):return sub(qm(a[n],a[n]),qm(a[n-1],a[n+1]))
def phipair(a):return(a[0]-a[1],a[1])
def pc(a,b,N):
    return [sum(a[j]*b[k-j] for j in range(max(0,k-len(b)+1),min(k,len(a)-1)+1)) for k in range(N+1)]
def report(name,n):
    log=(ROOT/(name+'.log')).read_text(encoding='utf8')
    src=(ROOT/(name+'.lean')).read_text(encoding='utf8')
    assert ': error:' not in log and 'sorryAx' not in log and 'native_decide' not in src
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
    assert len(rows)==n,(name,len(rows))
    out={}
    for t,raw in rows:
        axioms=[x.strip() for x in raw.split(',')]
        assert set(axioms)<= {'propext','Classical.choice','Quot.sound'},(t,axioms)
        out[t]=axioms
    return out
def main():
    started=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=Random(20261031713)
    hosts=[(u,r) for u in range(13) for r in range(26)]+[(rng.randint(1,80),rng.randint(0,80)) for _ in range(150)]
    for u,r in hosts:
        E=closed(u,r);a=inv(E);assert all(qs(x)>0 for x in a)
        tau=qm(qpow((1,-1),u),qpow((2,-2),r));assert a[-1]==tau
        margins=[lc(a,n) for n in range(1,len(a)-1)]
        if u or r>=6 or not r:
            assert all(qs(m)>=0 for m in margins),(u,r)
            ct['independent_positive_LC_hosts']+=1;ct['independent_LC_minors']+=len(margins)
        else:assert qs(margins[-1])<0
        sha.update(str((u,r,a[-1],margins)).encode())
    base=json.loads((ROOT/'ternary_forward_inverse_base_data.json').read_text())
    E=closed(0,6);a=inv(E);ms=[lc(a,n) for n in range(1,len(a)-1)]
    assert E==base['E'] and [list(phipair(v)) for v in a]==base['forward']
    assert [list(phipair(v)) for v in ms]==base['margins']
    budget=sub((2,1),qm((2,14),a[-1]))
    assert list(phipair(budget))==base['potential_margin'] and qs(budget)>0
    src=(ROOT/'TernaryForwardInverseBase.lean').read_text(encoding='utf8')
    props=[f'0 < (({v[0]}:ℝ)+({v[1]}:ℝ)*q)' for v in a]
    def ex(v):return f'(({v[0]}:ℝ)+({v[1]}:ℝ)*q)'
    props +=[f'{ex(a[i-1])}*{ex(a[i+1])} ≤ {ex(a[i])}^2' for i in range(1,len(a)-1)]
    props +=[f'2*(1+q+6*q)*{ex(a[-1])} ≤ (1+q)^2']
    assert (' ∧\n    '.join(props)) in src
    for r in range(1,6):assert qs(lc(inv(closed(0,r)),2*r-1))<0
    S2=[0,1,1];S3=[0,1,1,1];K=[0,0,0]+closed(1,2)
    for _ in range(180):
        u=rng.randint(0,20);r=rng.randint(0,30);alpha=rng.randint(1,35)
        N=alpha+2*(u+1)+3*(r+2)
        old=suffix_boxes(alpha,[2]*u+[3]*r)[:alpha+2*u+3*r+1]+[0]*8
        new=suffix_boxes(alpha,[2]*(u+1)+[3]*(r+2))[:N+1]
        assert len(old)==N+1
        B=[0]*(N+1)
        for j in range(r):
            for k,x in enumerate(closed(0,j)):B[j+k]+=x
        P=[0]*(N+1);P[0]=1
        for A,shift in [(closed(0,1),1),(closed(0,2),2),(pc(closed(0,2),B,N-5),5)]:
            for k,x in enumerate(A):P[k+shift]+=x
        assert [x+y for x,y in zip(pc(K,old,N),P)]==new
        H=[1]
        for n in range(1,N+1):H.append(sum(H[max(0,n-3):n]))
        Eold=[x-y for x,y in zip(H,old)];Enew=[x-y for x,y in zip(H,new)]
        s=[0]*(r+5)+closed(0,r+2)
        assert Enew==[x+y for x,y in zip(pc(K,Eold,N),pc(s,H,N))]
        ct['independent_positive_suffix_box_diagonal_hosts']+=1
        ct['independent_ALL_diagonal_identity_reads']+=2*(N+1)
        sha.update(str((alpha,u,r,new)).encode())
    qa_data=json.loads((ROOT/'audit_ternary_forward_inverse.json').read_text())
    assert qa_data['status']=='EXACT_QA_TERNARY_FORWARD_INVERSE_AND_POSITIVE_DIAGONAL_IDENTITIES'
    kernels={name:report(name,n) for name,n in [('TernaryForwardInverse',8),('TernaryForwardInverseBase',1),('TernaryDiagonalCompanion',3)]}
    files=['ternary_forward_inverse_and_diagonal_companion.tex','TernaryForwardInverse.lean','TernaryForwardInverse.log',
      'TernaryForwardInverseBase.lean','TernaryForwardInverseBase.log','TernaryDiagonalCompanion.lean','TernaryDiagonalCompanion.log',
      'build_ternary_forward_inverse_base.py','ternary_forward_inverse_base_data.json','audit_ternary_forward_inverse.py',
      'audit_ternary_forward_inverse.json','verify_ternary_forward_inverse.py',
      'probe_ternary_forward_inverse.py','probe_ternary_forward_inverse.json']
    out=dict(status='PASS_UNBOUNDED_TERNARY_FORWARD_INVERSE_AND_ACTUAL_DIAGONAL_IDENTITIES',new_scoped_reports=12,kernels=kernels,
      theorem='ALLu>=1,r>=0: ZERO-TRUNCATED forwardprefix of(1+z)^u[3]^r/(1+qz) throughdegreeu+2r is STRICTLYpositive/GLOBALLYLC. NOcountbound. Binaryextensionlowersonefinalcoefficient;ternaryextensionchangesTWOandhasEXACTlastminorphi²-2(phi+q*w)*tau. Completeunboundedtwo-countpotentialinductiontau=q^(2u)(2q²)^r. NOTthefullalternatingFPSquotient.',
      pure='Pureu0: ALLrpositiveprefix;globalLCIFF r0orr>=6. SingleEXPLICITdegree12base13coefficients/11minors/onepotentialinONEkernel. r1..5penultimateminorsexactlynegative. Unboundedextensionfromr6,NOparameterenumerationpremise.',
      companion='ALLactualalpha>=1,u/r>=0:SAMEpaddingdiagonalFnew=KFold+1+S3+S3²+z³S3²B_r;Enew=KEold+z³S3^(r+2)H3;Lnew=KLold+zS3^(r+2)+z³S3^(r+2)d3. COMPLETEpositivecommutationandsourcecompanionsretained.',
      formal_scope='12NEWreports:8golden/potential/terminal/monotonekernelsINCLUDINGunboundedtwo-Natinduction;ONEexplicitdegree12aggregatebase;3diagonalCommRingidentities. Standardaxiomsonly,noSorry/native. LCconvolution,coefficient/sortedwordidentificationandwholewrittensequenceinductionareNOTendtoendLeancompositionformalization. Independentbinomial/trinomialexpansion/alternatinginverseinQ(q),differentfromprimaryiterativeproduct/forwardrecurrenceinQ(phi);positiveSUFFIXBOXactualrebuilddifferentfromprimaryappend.',
      remaining='ActualstrongD-minordiagonalr2u,u>=33stillOPEN. NOenlargementofactualu4..32fullCfamilyfromauxiliarykernelalone. GeneralearlierC/fullA2/originalunamplifiedcoefficientUIOPEN. Firstunresolvedcount6unchanged.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',counts=dict(ct),QA=qa_data['counts'],
      independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-started,
      sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'ternary_forward_inverse_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)
if __name__=='__main__':main()
