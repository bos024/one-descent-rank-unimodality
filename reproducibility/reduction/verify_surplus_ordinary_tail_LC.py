"""Independent positive-box, reverse-division and bounded-inverse verification of ordinary tail LC."""
from pathlib import Path
import sys,json,re,hashlib
from itertools import accumulate
from random import Random
from collections import Counter
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
from verify_ordinary_golden_growth_source import infinite_ones
from verify_degree_boundary_CI_entrance import reverse_divided
from verify_physical_boundary_golden_C import reference,conv
from audit_arbitrary_Fibonacci_tail_late_C import sign,sub,add,mul,power,evaluate
Q=(-1,1);ONE=(1,0);ZERO=(0,0);PSI=(1,-1)
NAMES=['cumulative_head_bounds','cumulative_quotient_seed','cumulative_ratio_step','whole_cumulative_prefix_LC',
 'cumulative_source_startup_budgets','first_startup_payment','second_startup_payment',
 'reference_amplitude_boundary_budget','first_missing_ordinary_boundary_payment','constant_reference_density_excludes_strict_growth']
def kernels():
    src=(ROOT/'SurplusOrdinaryTail.lean').read_text();log=(ROOT/'SurplusOrdinaryTail.log').read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(x in log for x in ('error:','warning:','sorryAx','ofReduceBool','failed'))
    assert log.count('depends on axioms:')==10
    out={}
    for n in NAMES:
        m=re.search(re.escape("'SurplusOrdinaryTail."+n+"'")+r' depends on axioms: \[([^]]*)\]',log);assert m,n
        ax={a.strip() for a in m.group(1).split(',') if a.strip()};assert ax<={'propext','Classical.choice','Quot.sound'}
        out[n]=sorted(ax)
    return out
def main():
    qa=json.loads((ROOT/'audit_surplus_ordinary_tail_LC.json').read_text())
    assert qa['status']=='EXACT_QA_SURPLUS_ORDINARY_FULL_TAIL_LC_UNDER_AUDIT'
    rng=Random(20261031411);ct=Counter();sha=hashlib.sha256();profiles=[]
    for r in range(1,5):
        for cap in range(3,20):
            V=[cap]*r;h=(cap-1)*r
            for u in {max(16,h),max(16,h+2),max(16,2*h+1)}:profiles.append((u,V))
    for _ in range(70):
        V=sorted(rng.choices(range(3,24),k=rng.randint(1,7)));h=sum(t-1 for t in V)
        profiles.append((rng.randint(max(16,h),max(16,2*h)),V))
    for u,V in profiles:
        r=len(V);h=sum(t-1 for t in V);W=h+r;w=u+r;L=[1]
        for t in V:L=conv(L,[1]*t)
        E=L[:]
        for _ in range(u):E=conv(E,[1,1])
        CE=list(accumulate(E));d=len(E)-1;I=infinite_ones([2]*u+V,w+2+d+5)
        J=reverse_divided(L,u);assert len(J)==d
        c=mul(power(PSI,u),evaluate(L,(0,-1)))
        B=[(-I[w+2+s],I[w+1+s]) for s in range(d+3)]
        total=mul(Q,c)
        for s in range(d+3):
            if s<d:total=add(total,J[s])
            assert total==B[s]
            if s:assert sign(sub(B[s],B[s-1]))>=0
            if s and s<d+2:assert sign(sub(mul(B[s],B[s]),mul(B[s-1],B[s+1])))>=0
            rhs=add(B[s],mul(Q,B[s-1]) if s else ZERO)
            if s==0:rhs=add(rhs,mul(power(Q,2),c))
            assert rhs==(CE[s] if s<len(CE) else CE[-1],0)
            ct['independent_reverse_quotient_cumulative_source_and_LC_reads']+=1
        # Direct full bounded inverse, including its infinite constant tail.
        M=d+3
        for s in {-1,0,1,d//2,d-1,d+1}:
            acc=ZERO
            for j in range(1,M+1):
                idx=s+j;bs=B[idx] if idx<len(B) else B[-1]
                acc=add(acc,mul(power(Q,j),bs))
            acc=add(acc,mul(mul(power(Q,M+1),(1,1)),B[-1]))
            assert acc==(I[w+2+s],0)
            ct['independent_exact_bounded_geometric_inverse_including_constant_tail']+=1
        R=reference(V,w+2);x=R[W]-R[W-1];y=R[W+1]-R[W]
        A=x*x+x*y-y*y;assert 0<A<=R[W]<=R[w]
        ct['independent_reference_amplitude_boundary_budgets']+=1
        for alpha in {1,2,4,max(5,d//2),d+3}:
            F=suffix_boxes(alpha,[2]*u+V)[:alpha+2*u+W+1]+[0]
            FM=F.index(max(F));assert FM<=w+2+d-1
            for n in range(w+1,len(F)-1):
                assert F[n]**2>=F[n-1]*F[n+1]
                ct['independent_positive_box_ENTIRE_ordinary_LC_tail_minors']+=1
            for s in range(-1,d+3):
                N=w+2+s;idx=s-alpha+1
                loss=0 if idx<0 else (CE[idx] if idx<len(CE) else CE[-1])
                assert (F[N] if N<len(F) else 0)==I[N]-loss
                ct['independent_positive_box_exact_ALL_padding_ordinary_models']+=1
            ct['independent_positive_box_hosts']+=1
        sha.update(json.dumps([u,V,A,B[:3],I[w:w+3]],separators=(',',':')).encode());ct['independent_CI_profiles']+=1
    deps=['degree_boundary_CI_entrance_verification.json','all_padding_CI_entrance_verification.json',
          'ordinary_golden_growth_source_verification.json','physical_boundary_golden_C_verification.json',
          'homogeneous_reference_and_sharp_entrance_verification.json','hereditary_strong_late_C_verification.json']
    for name in deps:
        dep=json.loads((SOURCE/name).read_text())
        for f,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/f).read_bytes()).hexdigest()==digest,f
    files=['surplus_ordinary_tail_LC_proof.tex','SurplusOrdinaryTail.lean','SurplusOrdinaryTail.log',
           'audit_surplus_ordinary_tail_LC.py','audit_surplus_ordinary_tail_LC.json',
           'verify_surplus_ordinary_tail_LC.py','golden_signed_primitive_cut_closure.tex']+deps
    def fp(f):return ROOT/f if (ROOT/f).exists() else SOURCE/f
    out=dict(status='PASS_UNBOUNDED_SURPLUS_ORDINARY_COEFFICIENT_FULL_TAIL_LC',new_scoped_reports=10,kernels=kernels(),
      state_sha256=qa['state_sha256'],QA=qa['counts'],independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),
      new_finite_entrance_certificates=0,
      theorem='PROVED ALLactualnormalized1alpha2uV,ANYnonemptyV>=3,ALLpadding/counts/caps: u>=max(h,16) impliesordinaryF_N^2>=Fprev*Fnext atEVERYcentreN>=u+r+1,ENTIREtailthroughandbeyondallordinarymodes/support. No new finite entrance. This isordinarycoefficientLC onitsstatedtail,NOTcumulativeLC/relativeLC/originalcoreUI.',
      cumulative_quotient='PROVED actualordinarygoldendeficit B_s=q*c+cumJ_s ispositive/nondecreasing/eventuallyconstant andGLOBALordinaryLC. FullquotientJ ordinaryLC,notitspositiveprimitiveLC,isrequired. ExactB0=1-q²c retained;firstBminorpaidbyCIhead,andFULLcumulativeLCinduction propagatesALLcentres. Positiveprimitiveafterrank0isJ_(s>=1).',
      bounded_cut='PROVED boundedconstant-tail futureinverse andfinitecutlimit: truncateB afteritsfirstmaximalplateau,keepSAMEfirstmode/positiveprimitive;applyOLDfinitegeometriccutthenpassLCtoordinarycoefficientlimit. TRUEcumulativeE source differsfromB+qzB ONLYat0,q²c retained;startupusesM1=w+1,M2=E2+w+1. InitialphysicalcentreN=w+1paidSEPARATELY,notwrongzeroextendednegativeindex.',
      first_boundary='PROVED ALLcapacityreferenceR_W>=fixedCassiniA; r>=2 viaA<=117/50x<5/2x<=R_W, r1viaFib(L-2)-(-1)^(L+1)>=0. ThusfirstordinarydefectpaysANYsurplusboundaryw+1. Constantinfinite-initialreferenceafteritsfirstmode andREGISTEREDfinitepaddingordinarydensity excludealateractualfirstmode.',
      formal_scope='TENnewcleanstandardaxiomscopedreports,includingFULLarbitrary-prefixcumulativeLCinduction,entirehead/startup/reference/unit/modebudgets. Actualquotient/root/sourceidentities,geometricconvolutionandcutlimits,modeidentificationandfullactualassemblyWRITTEN,notend-to-endLeanactualcompositiontheorem. FiniteQAONLY,no new finite premise.',
      remaining='SurplusrelativeordinaryLC andordinaryminor>=referenceCassiniAremainOPENdespitefiniteQA. Generalactualdensityrecord,unseededcrossing,earlierC/fullA2/originalunamplifiedcoefficientUIOPEN. GeneralCfirstunresolvednononecount6unchanged.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',
      sha256={f:hashlib.sha256(fp(f).read_bytes()).hexdigest() for f in files})
    (ROOT/'surplus_ordinary_tail_LC_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('sha256','kernels')}),flush=True)
if __name__=='__main__':main()

