"""Independent positive-suffix and reverse-quotient verification of the earlier boundary."""
from pathlib import Path
import sys,json,hashlib,re
from itertools import accumulate
from random import Random
from collections import Counter
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
from verify_ordinary_golden_growth_source import infinite_ones
from verify_degree_boundary_CI_entrance import reverse_divided
from audit_arbitrary_Fibonacci_tail_late_C import sign,sub,add,mul,power,evaluate,absolute
Q=(-1,1);PHI=(0,1);ONE=(1,0)
NAMES=['previous_CI_units','degree_two_gap_payment','positive_head_gap_payment','multiple_factor_norm_payment',
       'large_degree_row_geometry','nonincreasing_CI_row_entry','boundary_C_read_guard','four_gap_all_shift_guard']

def conv(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c

def reference(V,N):
    suffix=[1];proper=[0]*(N+1)
    for t in reversed(V):
        for i,x in enumerate(suffix[:N+1]):proper[i]+=x
        suffix=conv(suffix,[0]+[1]*t)
    H=[1,1]
    while len(H)<=N:H.append(H[-1]+H[-2])
    full=conv(suffix,H)
    return [proper[n]+full[n] for n in range(N+1)]

def kernels():
    src=(ROOT/'PhysicalBoundaryGoldenC.lean').read_text();log=(ROOT/'PhysicalBoundaryGoldenC.log').read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(x in log for x in ('error:','warning:','sorryAx','ofReduceBool','failed'))
    assert log.count('depends on axioms:')+log.count('does not depend on any axioms')==8
    out={}
    for n in NAMES:
        prefix="'PhysicalBoundaryGoldenC."+n+"'"
        if prefix+' does not depend on any axioms' in log:out[n]=[];continue
        m=re.search(re.escape(prefix)+r' depends on axioms: \[([^]]*)\]',log);assert m,n
        ax={a.strip() for a in m.group(1).split(',') if a.strip()};assert ax<={'propext','Classical.choice','Quot.sound'};out[n]=sorted(ax)
    return out

def main():
    qa=json.loads((ROOT/'audit_physical_boundary_golden_C.json').read_text())
    assert qa['status']=='EXACT_QA_PHYSICAL_BOUNDARY_GOLDEN_D_AND_EARLIER_C_UNDER_AUDIT'
    ct=Counter();sha=hashlib.sha256();profiles=[]
    for t in range(3,18):
        for r in range(1,5):
            V=[t]*r;h=r*(t-1)
            for u in {0,1,max(0,h-4),h-2,h-1,h,h+1}:profiles.append((u,V))
    rng=Random(20261031206)
    for _ in range(100):
        V=sorted(rng.choices(range(3,19),k=rng.randint(1,7)));h=sum(t-1 for t in V);profiles.append((rng.randint(0,2*h),V))
    for u,V in profiles:
        r=len(V);W=sum(V);h=W-r;w=u+r;delta=h-u;L=[1]
        for t in V:L=conv(L,[1]*t)
        rho=mul(absolute(evaluate(L,(0,-1))),power(Q,h));atom=mul(power(PHI,2),rho)
        I=infinite_ones([2]*u+V,W+1);a=I[W-1]-I[W-2];b=I[W]-I[W-1];gap=(-b,a)
        if delta>=2 and u:
            J=reverse_divided(L,u);assert gap==add(PHI,J[delta-2]);ct['independent_reverse_quotient_boundary_identities']+=1
            if h>=3*u+3:assert a>=b
        elif delta>=2:assert (a,b)==(r,1)
        else:assert gap==sub(PHI,atom)
        exception=r==1 and V[0]%2 and delta<=1
        assert (sign(gap)<0)==bool(exception)
        R=reference(V,W+1);Gref=list(accumulate(R));rd=[0,0]+[R[n]-R[n-1] for n in range(2,len(R))]
        assert (-rd[W],rd[W-1])==sub(PHI,atom)
        for k in range(1,W-2):assert Gref[k]*rd[W-1]>=Gref[k-1]*rd[W];ct['independent_entire_reference_boundary_C_reads']+=1
        for alpha in {1,2,max(1,delta+1)}:
            F=suffix_boxes(alpha,[2]*u+V)[:alpha+2*u+W+1]+[0];G=list(accumulate(F));D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
            assert D[W]*a<=D[W-1]*b
            if exception:assert sign((-D[W],D[W-1]))<0;ct['independent_protected_odd_exception_edges']+=1
            elif D[W-1]:assert sign((-D[W],D[W-1]))>0;ct['independent_actual_physical_boundary_golden_edges']+=1
            else:assert D[W]==0
            for k in range(1,min(W-3,w+1)+1):
                assert G[k]*D[W-1]>=G[k-1]*D[W];ct['independent_actual_new_boundary_C_reads']+=1
            if u>=h-4:
                best=1
                for N in range(4,len(F)):
                    k=N-3
                    if G[k]*G[best-1]<G[best]*G[k-1]:best=k
                    if N>=W:
                        assert G[best]*D[N-1]>=G[best-1]*D[N];ct['independent_all_current_earlier_C_halfline_minima']+=1
                ct['independent_earlier_C_halfline_hosts']+=1
            ct['independent_actual_hosts']+=1
        sha.update(json.dumps([u,V,a,b,gap,rho],separators=(',',':')).encode());ct['independent_CI_profiles']+=1
    F=suffix_boxes(3,[2]*46+[12,18,20]);D=[F[n]-F[n-1] for n in (49,50,51)]
    assert D==qa['actual_D_LC_earlier_start_counter']['D'] and D[1]**2-D[0]*D[2]==-4885249599
    deps=['ordinary_golden_growth_source_verification.json','golden_tail_large_shift_C_verification.json',
          'four_subdegree_C_entrance_verification.json','homogeneous_reference_and_sharp_entrance_verification.json',
          'general_one_jump_analytic_C_verification.json','relative_C_inheritance_verification.json']
    for f in deps:
        dep=json.loads((SOURCE/f).read_text())
        for n,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/n).read_bytes()).hexdigest()==digest,n
    files=['physical_boundary_golden_D_and_C_proof.tex','PhysicalBoundaryGoldenC.lean','PhysicalBoundaryGoldenC.log',
           'audit_physical_boundary_golden_C.py','audit_physical_boundary_golden_C.json','verify_physical_boundary_golden_C.py',
           'finite_initial_ones_relative_derivative.tex']+deps
    def fp(f):return ROOT/f if (ROOT/f).exists() else SOURCE/f
    out=dict(status='PASS_UNIVERSAL_PHYSICAL_BOUNDARY_GOLDEN_D_AND_ONE_EARLIER_C_ENTRANCE',new_scoped_reports=8,kernels={'PhysicalBoundaryGoldenC':kernels()},
        state_sha256=qa['state_sha256'],QA=qa['counts'],independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),new_finite_entrance_certificates=0,
        boundary_D='PROVED ALL actual r>=2,ALLu/h/capacities/paddings: D_W<phiD_(W-1) ifpredecessorpositive,zerocurrentotherwise. Single factor also unlessODDt andu>=h-1; in that EXCEPTION exact protected gap=-q^(t-1) forEVERYpadding. Forr>=2 protected gap>=q^5,positive-headgap>=q^2; exact previous CI derivative has r units,notone. No finite premise.',
        actual_boundary_C='PROVED ALLactualprofiles/ALLpadding atCURRENTN=W,EVERYshiftR>=max(3,h-u-1). Boundary golden payment uses protected actual G prefix; exceptional onefactor uses OLDcompleteC. Applies outside all registered whole-arm wedges.',
        earlier_actual_halfline='PROVED ALLu>=h-4,ALLcapacities/counts/paddings: EVERYCshift>=3 atEVERYcurrentN>=W,ONEphysicalrankearlierthanoldW+1. Combines NEWboundaryC with OLDall-lateC. No new finite entrance premise.',
        earlier_reference_halfline='PROVED infinite-BINARY reference ofEVERYnonemptyV>=3: EVERYCshift>=3 atEVERYcurrentN>=W,earlierthanoldW+1. AtW,r>=2usesuniversalreferencegoldengap>=q^5 andallGref ratios>phi; onefactorusesOLDcomplete referenceC. General earlierN<WreferenceC OPEN.',
        derivative_LC_control=qa['actual_D_LC_earlier_start_counter'],
        formal_scope='EIGHT NEW scoped standard-axiom kernels for exact CI previous-unit arithmetic,two/all-factor payments,ALL-integer complementary row geometry,and complete read-domain guards. Existing ALL-prefix divided-head and density/C/golden/norm results reused,NOTrecounted. Actual root/model/CI extraction,mode/source and halfline assemblies written,not end-to-end Lean. Every finite profile QA ONLY.',
        remaining='General actual/reference C atN<W and shorter-shift boundaryC outsideu>=h-4 remain OPEN. Sharper count wedge stillstartsW+1unlesscoveredbytheNEWu>=h-4halfline. CompleteA2/original unamplified coefficientUI OPEN; full-C first unresolved nononecount6 unchanged. Actual derivative-LC atW is FALSE,so do not shift that separate theorem.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',sha256={f:hashlib.sha256(fp(f).read_bytes()).hexdigest() for f in files})
    (ROOT/'physical_boundary_golden_C_verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ('sha256','kernels')}),flush=True)

if __name__=='__main__':main()
