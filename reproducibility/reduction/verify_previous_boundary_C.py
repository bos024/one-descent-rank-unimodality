"""Independent positive-suffix verification and exact scope registration of W-1 C."""
from pathlib import Path
import sys,json,re,hashlib
from random import Random
from collections import Counter
from itertools import accumulate,product
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
from verify_ordinary_golden_growth_source import infinite_ones
from verify_physical_boundary_golden_C import reference,conv
from verify_degree_boundary_CI_entrance import reverse_divided
from audit_arbitrary_Fibonacci_tail_late_C import sign,sub,add,mul,power,evaluate,absolute
Q=(-1,1);P=(0,1);PSI=(1,-1);ONE=(1,0)
REF=['golden_tight_lower','two_factor_lower_margin','three_factor_odd_margin','three_factor_even_margins','even_capacity_exceptions',
     'fib_norm','binary_envelope_identity','large_fib_envelope','exact_three_four_four','exact_three_four_six','exact_three_six_four','exact_three_four']
ACT=['three_four_norm_lower','conjugate_atom_lower','positive_head_at_least_one','base_two_head_payment','base_one_head_payment',
     'previous_CI_bonus','earlier_symmetric_row_geometry','previous_boundary_read_guard','five_gap_all_shifts_guard','eight_gap_wedge_or_small','protected_previous_current']

def kernels(stem,names):
    src=(ROOT/(stem+'.lean')).read_text();log=(ROOT/(stem+'.log')).read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(x in log for x in ('error:','warning:','sorryAx','ofReduceBool','failed'))
    assert log.count('depends on axioms:')==len(names)
    out={}
    for n in names:
        m=re.search(re.escape("'"+stem+'.'+n+"'")+r' depends on axioms: \[([^]]*)\]',log);assert m,n
        ax={a.strip() for a in m.group(1).split(',') if a.strip()};assert ax<={'propext','Classical.choice','Quot.sound'};out[n]=sorted(ax)
    return out

def main():
    qa=json.loads((ROOT/'audit_previous_boundary_C.json').read_text())
    assert qa['status']=='EXACT_QA_PREVIOUS_BOUNDARY_REFERENCE_AND_ACTUAL_C_UNDER_AUDIT'
    ct=Counter();sha=hashlib.sha256();rng=Random(20261031214);profiles=[]
    for V in product(range(3,9),repeat=2):
        W=sum(V);N=W-1;R=reference(V,W);G=list(accumulate(R));D=[0,0]+[R[i]-R[i-1] for i in range(2,len(R))]
        for k in range(1,N-2):assert G[k]*D[N-1]>=G[k-1]*D[N];ct['independent_arbitrary_order_reference_C_reads']+=1
    for V in product(range(3,8),repeat=3):
        W=sum(V);N=W-1;R=reference(V,W);G=list(accumulate(R));D=[0,0]+[R[i]-R[i-1] for i in range(2,len(R))]
        for k in range(1,N-2):assert G[k]*D[N-1]>=G[k-1]*D[N];ct['independent_arbitrary_order_reference_C_reads']+=1
    for r in range(1,6):
        for t in range(3,18):
            V=[t]*r;h=(t-1)*r
            for u in {0,max(0,h-5),max(0,h-3),h-2,h-1,h,h+1}:profiles.append((u,V))
    for _ in range(140):
        V=sorted(rng.choices(range(3,20),k=rng.randint(2,8)));h=sum(t-1 for t in V);profiles.append((rng.randint(0,2*h),V))
    for u,V in profiles:
        r=len(V);h=sum(t-1 for t in V);W=h+r;N=W-1;delta=h-u;w=u+r
        if N<3:continue
        L=[1]
        for t in V:L=conv(L,[1]*t)
        rho=mul(absolute(evaluate(L,(0,-1))),power(Q,h));I=infinite_ones([2]*u+V,W)
        a=I[N-1]-I[N-2];b=I[N]-I[N-1]
        R=reference(V,W);Gref=list(accumulate(R));rd=[0,0]+[R[i]-R[i-1] for i in range(2,len(R))]
        b1=r-int(V[0]==3);rgap=add(sub(mul((b1,0),P),power(P,3)),mul(power(P,3),rho))
        assert rgap==(-rd[N],rd[N-1])
        for k in range(1,N-2):assert Gref[k]*rd[N-1]>=Gref[k-1]*rd[N];ct['independent_entire_reference_previous_boundary_reads']+=1
        if r>=2 and delta>=3:
            J=reverse_divided(L,u);c=mul(power(PSI,u),evaluate(L,(0,-1)));s=delta-3
            f=add(J[s],mul(c,power(PSI,s)))
            assert (-b,a)==add(rgap,f) and sign((-b,a))>0;ct['independent_reverse_quotient_previous_gap_identities']+=1
        for alpha in {1,2,max(1,delta+1)}:
            F=suffix_boxes(alpha,[2]*u+V)[:alpha+2*u+W+1]+[0];G=list(accumulate(F));D=[0,0]+[max(0,F[i]-F[i-1]) for i in range(2,len(F))]
            if r>=2 and delta>=3:
                assert D[N]*a<=D[N-1]*b
                if D[N-1]:assert sign((-D[N],D[N-1]))>0
                else:assert D[N]==0
                ct['independent_all_padding_previous_golden_edges']+=1
            elif delta<=2:assert F[:N+1]==R[:N+1]
            for k in range(1,min(N-3,w+1)+1):assert G[k]*D[N-1]>=G[k-1]*D[N];ct['independent_actual_previous_large_shift_reads']+=1
            if u>=h-5:
                for k in range(1,N-2):assert G[k]*D[N-1]>=G[k-1]*D[N];ct['independent_actual_previous_ALLshift_reads']+=1
            if u>=h-4:
                best=1
                for cur in range(4,len(F)):
                    k=cur-3
                    if G[k]*G[best-1]<G[best]*G[k-1]:best=k
                    if cur>=N:
                        assert G[best]*D[cur-1]>=G[best-1]*D[cur];ct['independent_two_rank_earlier_actual_halfline_minima']+=1
                ct['independent_two_rank_earlier_actual_halfline_hosts']+=1
            ct['independent_actual_hosts']+=1
        sha.update(json.dumps([u,V,rgap,a,b],separators=(',',':')).encode());ct['independent_CI_profiles']+=1
    # The full lists used by the four finite Lean prefix reductions are independently recomputed.
    finite=[]
    for V in ([3,4,4],[3,4,6],[3,6,4],[3,4]):
        N=sum(V)-1;R=reference(V,N);G=list(accumulate(R));D=[0,0]+[R[i]-R[i-1] for i in range(2,len(R))]
        margins=[G[k]*D[N-1]-G[k-1]*D[N] for k in range(1,N-2)];assert min(margins)>=0
        finite.append(dict(V=V,current=N,derivative_pair=D[N-1:N+1],ALL_C_margins=margins))
    deps=['physical_boundary_golden_C_verification.json','ordinary_golden_growth_source_verification.json',
          'golden_tail_large_shift_C_verification.json','homogeneous_reference_and_sharp_entrance_verification.json',
          'general_one_jump_analytic_C_verification.json','relative_C_inheritance_verification.json',
          'sharp_CI_count_wedge_verification.json','multitail_binary_prefix_finite_principle_verification.json']
    for f in deps:
        dep=json.loads((SOURCE/f).read_text())
        for n,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/n).read_bytes()).hexdigest()==digest,n
    files=['previous_boundary_C_proof.tex','ReferencePreviousBoundaryC.lean','ReferencePreviousBoundaryC.log',
           'ActualPreviousBoundaryC.lean','ActualPreviousBoundaryC.log','audit_previous_boundary_C.py',
           'audit_previous_boundary_C.json','verify_previous_boundary_C.py','finite_initial_ones_relative_derivative.tex']+deps
    def fp(f):return ROOT/f if (ROOT/f).exists() else SOURCE/f
    out=dict(status='PASS_SECOND_EARLIER_REFERENCE_AND_ACTUAL_C_BOUNDARY_AND_EIGHT_GAP_COROLLARY',new_scoped_reports=23,
        kernels={'ReferencePreviousBoundaryC':kernels('ReferencePreviousBoundaryC',REF),'ActualPreviousBoundaryC':kernels('ActualPreviousBoundaryC',ACT)},
        state_sha256=qa['state_sha256'],QA=qa['counts'],independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),
        new_finite_entrance_certificates=4,new_finite_reference_exception_prefixes=finite,
        reference='PROVED EVERY infinite-BINARY reference V>=3,arbitraryorder/count/capacities: EVERYshift>=3 atEVERYcurrentN>=W-1. Exact two-top-numerator gap and all-capacity norm classify all butV3T and THREE ordered finite profiles; ALLT>=3 Cassini envelope gives Fib(T-3)+2(-1)^(T+1), with T4 separately actual-prefix paid. FOUR constant exception-prefixes directly Lean kernel-reconstructed. No sampled-host logical premise.',
        actual_golden_edge='PROVED ALLr>=2,delta=h-u>=3,ALLcapacities/counts/paddings: D_(W-1)<phiD_(W-2) whenpreviouspositive,zerootherwise. Exact previous CI bonus binom(r+1,2)-epsilon retained. Full monotone divided head and complementary symmetric-row cone cover ALLdegrees. Ifdelta<=2,use exact protected reference C instead; do not assert its golden edge in the exception families.',
        actual_boundary='PROVED ALLactualprofiles/paddings,CURRENTN=W-1,EVERYshiftR>=max(3,h-u-2). HenceALLshifts at thatcurrent wheneveru>=h-5. OnefactorusesOLDcompleteC;protected delta<=2 usesNEWreference theorem.',
        actual_halfline='PROVED ALLu>=h-4,EVERYactualCshift>=3 atEVERYcurrentN>=W-1. This moves the continuous halfline TWOphysicalranks earlier than oldW+1. Foru=h-5 ONLY boundaryW-1 is added; currentW is still an explicit open one-rank gap, not silently filled.',
        eight_gap_corollary='PROVED asCOROLLARYofOLDsharpwedge plusOLDnonbinaryweight32completeC: ALLu>=h-8 haveEVERYactualCshift>=3 atEVERYcurrentN>=W+1. Ifwedgefails anddelta<=8 thenW<=29. This is an extraction from existing theorems,not a new sampled finite entrance.',
        formal_scope='TWENTY-THREE NEW scoped standard-axiom reports:12reference incl full ALL-natural Fibonacci identities/large-index payment andFOUR exact finite reference-prefix reductions;11actual incl intervalnorm/head/CI/row/read/first-loss/eight-gap guards. Actual model/root/CI identification and complete sequence assemblies WRITTEN,not end-to-end Lean actual arms. All remaining finite profiles QA ONLY.',
        remaining='General actual/reference C atN<W-1 and shorter boundary shifts outside its read guard remain OPEN. u=h-5 currentW gap OPEN. The larger whole-arm wedge still startsW+1 outside the strongeru>=h-4halfline. GeneralA2/original unamplified coefficientUI OPEN; fullC first unresolved nononecount6 unchanged. Neither cumulativeLC nor numerical nonfailure is substituted for coefficientUI.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',sha256={f:hashlib.sha256(fp(f).read_bytes()).hexdigest() for f in files})
    (ROOT/'previous_boundary_C_verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ('sha256','kernels','new_finite_reference_exception_prefixes')}),flush=True)

if __name__=='__main__':main()
