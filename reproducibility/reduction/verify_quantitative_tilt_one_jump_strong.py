"""Independent positive-box and exact normalized-tilt audit of all one-factor crossings."""
from pathlib import Path
import sys,json,re,hashlib
from fractions import Fraction as Q
from collections import Counter
from itertools import accumulate
from random import Random
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
from verify_physical_boundary_golden_C import reference
from audit_arbitrary_Fibonacci_tail_late_C import sign
NAMES=['entire_kernel_row','quantitative_normalized_tilt','finite_weighted_reference_margin',
 'additive_margin_LR_transfer','weighted_negative_coefficient','all_capacity_polynomial_payment',
 'fibonacci_middle_budget','fibonacci_linear_budget','capacity_three_tilt_seed']
def kernels():
    src=(ROOT/'QuantitativeTiltStrongOneJump.lean').read_text();log=(ROOT/'QuantitativeTiltStrongOneJump.log').read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(x in log for x in ('error:','warning:','sorryAx','ofReduceBool','failed'))
    assert log.count('depends on axioms:')==9
    out={}
    for n in NAMES:
        m=re.search(re.escape("'QuantitativeTiltStrongOneJump."+n+"'")+r' depends on axioms: \[([^]]*)\]',log);assert m,n
        ax={a.strip() for a in m.group(1).split(',') if a.strip()};assert ax<={'propext','Classical.choice','Quot.sound'}
        out[n]=sorted(ax)
    return out
def at_least_qsquare(v):
    v=Q(v)
    return sign((v.numerator-2*v.denominator,v.denominator))>=0
def box(alpha,u,V,ct):
    W=sum(V);F=suffix_boxes(alpha,[2]*u+V)[:alpha+2*u+W+1]+[0];G=list(accumulate(F))
    D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];a,b=D[W:W+2]
    if b>a>0:
        for k in range(1,W+1):
            assert at_least_qsquare(Q(a*G[k]-b*G[k-1],a))
            ct['independent_actual_additive_strong_prefix_reads']+=1
        for n in range(W,len(F)-1):
            assert F[n]**2>=F[n-1]*F[n+1];ct['independent_actual_entire_ordinary_LC_tail_reads']+=1
        ct['independent_actual_strict_entries']+=1
    best=1
    for N in range(4,len(F)):
        k=N-3
        if G[k]*G[best-1]<G[best]*G[k-1]:best=k
        if N>=W+1:
            assert G[best]*D[N-1]>=G[best-1]*D[N];ct['independent_entire_late_C_minima']+=1
    ct['independent_actual_hosts']+=1
    return F,G,D
def main():
    qa=json.loads((ROOT/'audit_quantitative_tilt_one_jump_strong.json').read_text())
    assert qa['status']=='EXACT_QA_QUANTITATIVE_TILT_AND_ONEJUMP_STRONG_UNDER_AUDIT'
    ct=Counter();rng=Random(20261031352);sha=hashlib.sha256()
    fib=[0,1]
    for _ in range(200):fib.append(sum(fib[-2:]))
    for L in range(3,130):
        for a in {Q(1),Q(7,10),Q(21,25),Q(rng.randint(1,79),80)}:
            T=[Q(1),Q(1)]
            for n in range(2,L+1):T.append(T[-1]+a**(n-2)*fib[n])
            val=fib[L]*T[L]-a*(fib[L+1]-1)*T[L-1]
            assert val>0 and val>=(4 if L==3 else fib[L-4]+4)
            ct['independent_full_negative_coefficient_budget_bounds']+=1
    for u in range(5,86,4):
        for L in sorted({u+2,u+7,3*u//2,2*u-1}):
            if L<u+2:continue
            R=reference([L],L+1);GR=list(accumulate(R))
            rd=[0,0]+[R[n]-R[n-1] for n in range(2,len(R))]
            assert rd[L]==fib[L] and rd[L+1]==fib[L+1]-1
            lam=Q(rd[L+1],rd[L])
            for alpha in {1,3,2*u+3}:
                F,G,D=box(alpha,u,[L],ct);A,B=D[L:L+2]
                if B>A>0:
                    rho=[Q(D[n],rd[n]) for n in range(2,L+2)]
                    for n in range(1,len(rho)-1):
                        assert rho[n]**2>=rho[n-1]*rho[n+1]
                        ct['independent_onejump_relative_density_LC_reads']+=1
                    assert all(rho[i+1]<=rho[i] for i in range(len(rho)-1))
                    a=rho[-1]/rho[-2];mu=Q(B,A);assert 0<a<=1 and mu==a*lam>1
                    T=[Q(1),Q(1)]
                    for n in range(2,L+1):T.append(T[-1]+a**(n-2)*rd[n])
                    GT=list(accumulate(T));assert T[L]-mu*T[L-1]>=Q(4,fib[L])
                    assert F[L]*T[L-1]>=F[L-1]*T[L]
                    for k in range(1,L+1):
                        assert F[k]>=T[k] and G[k]>=GT[k]
                        assert G[k]*GT[k-1]>=G[k-1]*GT[k]
                        assert at_least_qsquare(GT[k]-mu*GT[k-1])
                        def K(n):return Q(1) if n==0 else 2*(1-a)+(n-1)*(1-a)**2
                        H=[Q(1)]+[GR[i]-lam*GR[i-1] for i in range(1,k+1)]
                        rhs=sum(K(k-i)*a**i*H[i] for i in range(k+1))+(a*a-1)*(1+k*(1-mu))
                        assert rhs==a*a*(GT[k]-mu*GT[k-1])
                        assert sum(K(k-i)*a**i for i in range(k+1))==1+k*(1-a)
                        ct['independent_exact_full_tilt_row_and_shared_atom_identities']+=1
                    ct['independent_strict_actual_density_transfers']+=1
                V=[L]
                for step in range(2):
                    V.append(rng.randint(V[-1],max(V[-1],min(2*u-1,V[-1]+u//5))))
                    SF,SG,SD=box(alpha,u,V,ct);W=sum(V)
                    if SD[W+1]>SD[W]>0 and L-1-u>=5:
                        ct['independent_new_onefactor_seed_strict_suffixes']+=1
                sha.update(json.dumps([alpha,u,L,V,SD[sum(V):sum(V)+2]],separators=(',',':')).encode())
    w=qa['new_seed_witness'];F,G,D=box(w['alpha'],w['u'],w['V'],ct)
    assert sum(w['V'])==w['W'] and D[w['W']:w['W']+2]==w['pair']
    deps=['hereditary_strong_late_C_verification.json','general_one_jump_analytic_C_verification.json',
          'relative_C_inheritance_verification.json','two_factor_complete_entrance_verification.json']
    for name in deps:
        dep=json.loads((SOURCE/name).read_text())
        for f,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/f).read_bytes()).hexdigest()==digest,f
    files=['quantitative_tilt_one_jump_strong_proof.tex','QuantitativeTiltStrongOneJump.lean','QuantitativeTiltStrongOneJump.log',
           'audit_quantitative_tilt_one_jump_strong.py','audit_quantitative_tilt_one_jump_strong.json',
           'verify_quantitative_tilt_one_jump_strong.py']+deps
    def fp(f):return ROOT/f if (ROOT/f).exists() else SOURCE/f
    out=dict(status='PASS_QUANTITATIVE_NORMALIZED_TILT_AND_ALL_ONE_FACTOR_CROSSING_STRONG_LATE_C',
      new_scoped_reports=9,kernels=kernels(),state_sha256=qa['state_sha256'],QA=qa['counts'],
      independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),new_finite_entrance_certificates=0,
      quantitative_tilt='PROVED ANYnormalizedreference withALLneededcumulativeadditivemargins>=c,0<=c<=1: EVERYnormalizedgeometrictilta in(0,1] preservesSAMEc whennewcurrentratio>=1. FULLrowinduction/EXACTnonnegativefactorizationkeepinitialatom1. NormalizedrelativeLC descendants inheritSAMEc byTWICEcumulativeLR+coordinatewisedomination. No two-case threshold or sampled premise.',
      ordinary_tilt_seed='PROVED ALLL>=3,ALLa in[0,1]: FibL*T_L-a(Fib(L+1)-1)*T_(L-1)>=4. COMPLETEarbitrarydegreecoefficientformula;ENTIREnegativeFibonaccibudget sumsFib(L-1)-2; lastcoefficientnonnegative;ALLL>=4 lowerboundFib(L-4)+4, L3exact4. Not finite interpolation.',
      onefactor_strong='PROVED ALLactual1alpha2uL withL-1>u>=1,ALLpadding: conditionalSTRONGphysicalentranceatW=L. OLDonejumpnormalizedrelativeDLC throughFIRSTDmode appliesbecauseu<=L-2; NEWquantitativetiltretainsALLGreads>=q^2 incllastTWO,NEWordinarytiltseedtransfersviaLR. UniversalDLC+ordinarytailLCgivetheENTIREordinaryLCtailfromL.',
      arbitrary_suffix='PROVED ALLactual1alpha2uV withFIRSTnonbinarycapacity>=u+2,ARBITRARYsortedlatercaps/counts/padding: EVERYactualC fromcurrentN>=FINALW+1. NEWstrongseed permitshereditaryextension;ordinarycompleteCforonejumpALONEwasinsufficient. Entireone-factorfirstcrossingbranchofremaininglargeu lateC NOWELIMINATED.',
      residual='Generalpossiblelargeu lateCfailure musthaveFIRSTnonbinarycapacity<=u+1,FIRSTprefixdegree>u ofatleastTWOfactors,failingseedcone,andAT MOSTSIXlaternonbinaryfactors. Thatprefix/uandearlierCremainUNBOUNDED/OPEN. FullA2/originalunamplifiedcoefficientUIOPEN;fullCfirstunresolvedcount6unchanged.',
      new_coverage_witness=w,
      formal_scope='NINEnewcleanstandardaxiomscopedreports:FULLtiltrowandFibonaccisuminductions,exacttiltfactorization,finiteweightedmargin/LRtransfer,WHOLEnegativecoefficientbudgetandL3seed. All-capacitycoefficientidentification/density/reference/actualsequenceassemblyWRITTEN;notend-to-endLeancompositiontheorem. FiniteQAONLY,no new finite entrance.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',
      sha256={f:hashlib.sha256(fp(f).read_bytes()).hexdigest() for f in files})
    (ROOT/'quantitative_tilt_one_jump_strong_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('sha256','kernels')}),flush=True)
if __name__=='__main__':main()

