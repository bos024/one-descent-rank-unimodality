"""Independent suffix-box/reference audit; the universal actual density-record assertion stays open."""
from pathlib import Path
import sys,json,re,hashlib
from fractions import Fraction as Q
from itertools import product,accumulate
from collections import Counter
from random import Random
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
from verify_physical_boundary_golden_C import reference
from audit_arbitrary_Fibonacci_tail_late_C import sign,sub,mul,power,add
NAMES=['interval_split','positive_golden_atom_budgets','head_interval_nonnegative','head_interval_positive',
 'zero_head_interval_positive','one_head_interval_positive','complete_head_plus_alternating_tail_window',
 'all_current_window_geometry','generic_ordinary_tilt_seed']
def kernels():
    src=(ROOT/'ReferenceGoldenPrefix.lean').read_text();log=(ROOT/'ReferenceGoldenPrefix.log').read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(x in log for x in ('error:','warning:','sorryAx','ofReduceBool','failed'))
    assert log.count('depends on axioms:')==9
    out={}
    for n in NAMES:
        m=re.search(re.escape("'ReferenceGoldenPrefix."+n+"'")+r' depends on axioms: \[([^]]*)\]',log);assert m,n
        ax={a.strip() for a in m.group(1).split(',') if a.strip()};assert ax<={'propext','Classical.choice','Quot.sound'}
        out[n]=sorted(ax)
    return out
def main():
    qa=json.loads((ROOT/'audit_reference_ordinary_golden_prefix.json').read_text())
    assert qa['status']=='EXACT_QA_REFERENCE_ORDINARY_GOLDEN_PREFIX_AND_GENERAL_RECORD_CRITERION_UNDER_AUDIT'
    ct=Counter();sha=hashlib.sha256();rng=Random(20261031389)
    profiles=[]
    for r in range(1,5):profiles.extend(product(range(3,8),repeat=r))
    profiles += [tuple(rng.choices(range(3,26),k=rng.randint(2,8))) for _ in range(100)]
    for V in profiles:
        W=sum(V);R=reference(V,W+8);H=[(R[0],0)]+[(R[n],-R[n-1]) for n in range(1,len(R))]
        for n in range(2,W+1):
            assert sign(H[n])>0;ct['independent_arbitrary_order_ordinary_golden_prefix_reads']+=1
        tail=(0,0)
        for k in range(8):
            assert H[W+k]==mul(power((1,-1),k),H[W]);tail=add(tail,H[W+k])
            assert sign(sub(tail,mul(power((-1,1),2),H[W])))>=0
            ct['independent_exact_alternating_tail_and_partial_margin_reads']+=1
        rd=[0,0]+[R[n]-R[n-1] for n in range(2,len(R))];lam=Q(rd[W+1],rd[W])
        for a in {Q(1),Q(2,3),Q(4,5)}:
            mu=a*lam
            if mu<=1:continue
            T=[Q(1),Q(1)]
            for n in range(2,W+1):T.append(T[-1]+a**(n-2)*rd[n])
            assert T[W]>mu*T[W-1]
            h=[Q(1)]+[R[n]-lam*R[n-1] for n in range(1,W+1)]
            assert min(h[2:])>0 and 1+a-mu>=0
            rhs=a**W*h[W]+(1-a)*sum(a**i*h[i] for i in range(W))+(a*a-1)*(1-mu)
            assert rhs==a*a*(T[W]-mu*T[W-1]);ct['independent_generic_reference_tilt_seed_identifications']+=1
        sha.update(json.dumps([V,R[W-2:W+2]],separators=(',',':')).encode())
    failures=[]
    for _ in range(160):
        V=sorted(rng.choices(range(3,22),k=rng.randint(2,8)));h=sum(t-1 for t in V);W=sum(V)
        u=rng.randint(max(1,(h+1)//3),h-1);R=reference(V,W+1);r=[0,0]+[R[n]-R[n-1] for n in range(2,len(R))]
        for alpha in {1,3,2*u+h}:
            F=suffix_boxes(alpha,[2]*u+V)[:alpha+2*u+W+1]+[0];G=list(accumulate(F));D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
            A,B=D[W:W+2]
            if not B>A>0:continue
            ct['independent_actual_strict_entrances']+=1
            a=Q(B*r[W],A*r[W+1]);rho=[Q(D[j],r[j]) for j in range(2,W+1)]
            record=a<=1 and all(rho[j+1]>=a*rho[j] for j in range(len(rho)-1))
            if not record:
                failures.append(dict(alpha=alpha,u=u,V=V))
                ct['independent_record_condition_failures_NOT_general_theorem_failures']+=1
                continue
            ct['independent_actual_record_conditioned_entrances']+=1
            mu=Q(B,A)
            assert F[W]>mu*F[W-1]
            for k in range(1,W+1):
                v=Q(A*G[k]-B*G[k-1],A)
                assert sign((v.numerator-2*v.denominator,v.denominator))>=0
                ct['independent_record_conditioned_strong_cumulative_reads']+=1
            for n in range(W,len(F)-1):
                assert F[n]**2>=F[n-1]*F[n+1];ct['independent_record_conditioned_entire_ordinary_LC_tail']+=1
            best=1
            for N in range(4,len(F)):
                k=N-3
                if G[k]*G[best-1]<G[best]*G[k-1]:best=k
                if N>=W+1:
                    assert G[best]*D[N-1]>=G[best-1]*D[N]
                    ct['independent_record_conditioned_all_late_C_minima']+=1
    deps=['quantitative_tilt_one_jump_strong_verification.json','hereditary_strong_late_C_verification.json',
          'two_factor_complete_entrance_verification.json','homogeneous_reference_and_sharp_entrance_verification.json']
    for name in deps:
        dep=json.loads((SOURCE/name).read_text())
        for f,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/f).read_bytes()).hexdigest()==digest,f
    files=['reference_ordinary_golden_prefix_proof.tex','ReferenceGoldenPrefix.lean','ReferenceGoldenPrefix.log',
           'audit_reference_ordinary_golden_prefix.py','audit_reference_ordinary_golden_prefix.json',
           'verify_reference_ordinary_golden_prefix.py',
           'probe_physical_entry_density_record.py','probe_physical_entry_density_record.json']+deps
    def fp(f):return ROOT/f if (ROOT/f).exists() else SOURCE/f
    out=dict(status='PASS_ALL_REFERENCE_ORDINARY_GOLDEN_PREFIX_AND_GENERAL_CONDITIONAL_DENSITY_RECORD_C_ENTRANCE',
      new_scoped_reports=9,kernels=kernels(),state_sha256=qa['state_sha256'],QA=qa['counts'],
      independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),new_finite_entrance_certificates=0,
      reference='PROVED EVERYinfiniteBINARYreference withANYorderednonbinaryV>=3,ALLcaps/counts: F_n>phiFprev forEVERY2<=n<=W. COMPLETEarbitrarywordinduction:oldpositiveheadplusFULLalternatingtailwindow;ONLYW3scalarcasepaidbyEXACTq^6>0,ALLappendcaps. No finite exception premise.',
      generic_tilt_seed='PROVED EVERYsuchreference,EVERYnormalizedgeometrictilta in(0,1] withmu=a*r_(W+1)/r_W>1: ordinarytiltedF_W>muFprev. FULLone-cumulativeatomidentity;keep rank0/1TOGETHER,1+a-mu>=1-a>=0. Alllaterprefixordinaryresidualspositive byNEWreferencegoldenprefix,correctionnonnegative. Not limited toonefactor.',
      conditional_actual='PROVED SUFFICIENT actualphysicalentrycriterion: currentnormalizedDdensityratioa_N<=1 andisRECORDMINIMUMoverALLpastreadratios3..W. DoesNOTrequirefullrelativeLC. QuantitativeGtilt+twicecumulativeLR paysALLstrongGreads>=q^2;NEWgenericordinarytiltseed+oneLR paysF_W;universalDLCintegratesEVERYactualCfromW+1. Nonincreasing/clippedentryautomatic.',
      density_record_universal='OPEN. No proof thatEVERYactualstrictlygrowingphysicalentrancesatisfiesrecordcondition. Finite5714entrance/699345pastreadnonfailureisONLYdiagnostic; independentconditionedtestsalsoONLYQA. General lateC isNOTdeclaredproved.',
      independent_record_counterexamples=failures,
      formal_scope='NINEnewcleanstandardaxiomreports;FULLunboundedfiniteintervalhead/tailwindowcaseproof inclW3/allindexguards;genericordinarytiltseedalgebra. Reference/source/numerator/tailgeometricidentityandwordassembly,actualdensityLRandsequenceintegrationWRITTEN,notend-to-endactualLean. No finite logical premise.',
      remaining='Universalactualdensityrecordhypothesis,unseededcrossing,earlierC/fullA2/originalunamplifiedcoefficientUIremainOPEN. FirstunresolvedfullCnononecount6unchanged.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',
      sha256={f:hashlib.sha256(fp(f).read_bytes()).hexdigest() for f in files})
    (ROOT/'reference_ordinary_golden_prefix_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('sha256','kernels')}),flush=True)
if __name__=='__main__':main()

