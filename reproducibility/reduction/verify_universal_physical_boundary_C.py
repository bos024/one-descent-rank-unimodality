"""Independent positive suffix-box checks of universal actual C from W."""
from pathlib import Path
import sys,json,hashlib,re
from fractions import Fraction as Q
from itertools import accumulate
from random import Random
from collections import Counter
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
from verify_physical_boundary_golden_C import reference
from verify_ordinary_golden_growth_source import infinite_ones
from audit_arbitrary_Fibonacci_tail_late_C import sign
NAMES=['maximal_margin_normalized_tilt','moving_ratio_unit_margin','low_ratio_cumulative_margin',
 'margin_at_two_edge_maximum','two_edge_ratio_cap','positive_window_cap_transfer',
 'positive_support_window_endpoint','previous_reference_CDF_margin','all_large_degree_boundary_rows',
 'previous_unit_pays_boundary_nondecrease','small_binary_boundary_complement_weight32','late_owner_source_read_guard']

def kernels():
    src=(ROOT/'UniversalPhysicalBoundaryC.lean').read_text();log=(ROOT/'UniversalPhysicalBoundaryC.log').read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(x in log for x in ('error:','warning:','sorryAx','ofReduceBool','failed'))
    assert log.count('depends on axioms:')==12
    out={}
    for n in NAMES:
        m=re.search(re.escape("'UniversalPhysicalBoundaryC."+n+"'")+r' depends on axioms: \[([^]]*)\]',log);assert m,n
        ax={a.strip() for a in m.group(1).split(',') if a.strip()};assert ax<={'propext','Classical.choice','Quot.sound'}
        out[n]=sorted(ax)
    return out

def geq2(v):
    v=Q(v);return sign((v.numerator-2*v.denominator,v.denominator))>=0

def box(alpha,u,V):
    W=sum(V);F=suffix_boxes(alpha,[2]*u+V)[:alpha+2*u+W+1]+[0]
    return F,list(accumulate(F)),[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]

def host(alpha,u,V,ct):
    F,G,D=box(alpha,u,V);W=sum(V);h=W-len(V);A,B=D[W-1:W+1]
    if u>=5 and h>u:
        for n in range(W-1,len(F)-1):
            assert F[n]**2>=F[n-1]*F[n+1];ct['independent_ordinary_LC_entire_W_minus_one_tail']+=1
        if len(V)>=2 and B>A>0:
            assert sign((-B,A))>0
            for k in range(1,W):
                assert geq2(G[k]-Q(B,A)*G[k-1]);ct['independent_FULL_strong_boundary_prefix_q2_reads']+=1
    # Complete current-tail C via each exact running minimum, all shifts >=3.
    idx=1
    best=1
    for n in range(max(W,4),len(F)):
        while idx<=n-3:
            if G[idx]*G[best-1]<G[best]*G[idx-1]:best=idx
            idx+=1
        assert G[best]*D[n-1]>=G[best-1]*D[n]
        ct['independent_C_running_minimum_reads_N_ge_W']+=1
        ct['independent_C_logical_all_shift_reads']+=n-3
    ct['independent_actual_hosts']+=1
    return F,G,D

def main():
    qa=json.loads((ROOT/'audit_universal_physical_boundary_C.json').read_text())
    assert qa['status']=='EXACT_QA_UNIVERSAL_PHYSICAL_BOUNDARY_C_UNDER_AUDIT'
    rng=Random(20261031489);ct=Counter();sha=hashlib.sha256();witnesses=[]
    for L in range(3,70):
        R=reference([L],L+1);G=list(accumulate(R));d=[0,0]+[R[n]-R[n-1] for n in range(2,len(R))]
        lam=Q(d[L],d[L-1]);assert 1<=lam<=2
        for k in range(1,L):
            assert G[k]-lam*G[k-1]>=2-lam
        for a in {Q(1),Q(4,5),Q(19,20)}:
            mu=a*lam
            if mu<=1:continue
            F=[Q(1),Q(1)]
            for n in range(2,L):F.append(F[-1]+a**(n-2)*d[n])
            GT=list(accumulate(F))
            for k in range(1,L):
                assert GT[k]-mu*GT[k-1]>=2-mu
                ct['independent_positive_reference_maximal_tilt_margin_reads']+=1
    # Different generation: distribute surplus degree first, append first crossing,
    # and retain all intermediate old/new words in the two-layer induction.
    for _ in range(120):
        u=rng.randint(5,65);r=rng.randint(1,max(1,u//3));h=rng.randint(2*r,u)
        ds=[2]*r
        for j in range(h-2*r):ds[rng.randrange(r)]+=1
        V=sorted(d+1 for d in ds);low=max(V[-1],u-h+2)
        V.append(rng.randint(low,max(low,2*u)))
        for alpha in {1,2,u+h+3}:
            VV=V[:];old=host(alpha,u,VV,ct)
            for step in range(3):
                a=sum(VV);t=rng.randint(VV[-1],max(VV[-1],2*u+1));b=a+t
                new=host(alpha,u,VV+[t],ct);F,G,D=old;NF,NG,ND=new
                A,B=ND[b-1:b+1]
                if B>A>0:
                    assert all(D[k]>0 for k in range(a-1,b))
                    mu=Q(B,A);cap=max(Q(1),Q(D[a],D[a-1]),Q(D[a+1],D[a]))
                    assert mu<=cap and B*F[b-2]<=A*F[b-1]
                    for k in range(1,a):
                        assert geq2(G[k]-cap*G[k-1]);ct['independent_TWO_edge_maximum_old_G_payments']+=1
                    for k in range(a,b-1):
                        assert B*F[k-1]<=A*F[k] and geq2(G[k]-mu*G[k-1])
                        ct['independent_ordinary_LC_extended_G_payments']+=1
                    ct['independent_strict_boundary_hereditary_transfers']+=1
                VV=VV+[t];old=new
            sha.update(json.dumps([alpha,u,V,VV,ND[b-1:b+1]],separators=(',',':')).encode())
    # Onefactor protected odd exception and its first twofactor transfer are separate.
    for u in range(5,46):
        for L in {u+2,u+3,2*u-1}:
            for alpha in {1,u+L+2}:
                F,G,D=host(alpha,u,[L],ct)
                if D[L]>D[L-1]>0:
                    mu=Q(D[L],D[L-1])
                    if L-1-u>=2:
                        assert sign((-mu.numerator,mu.denominator))>0
                        for k in range(1,L):assert G[k]-mu*G[k-1]>=2-mu
                        ct['independent_actual_onefactor_maximal_margin_transfers']+=1
                    else:
                        assert G[:L+1]==list(accumulate(reference([L],L)))
                        ct['independent_protected_onefactor_degree_one_exceptions']+=1
                t=L;NF,NG,ND=host(alpha,u,[L,t],ct);b=L+t;A,B=ND[b-1:b+1]
                if B>A>0:
                    mu=Q(B,A);assert sign((-B,A))>0
                    for k in range(1,L):assert geq2(G[k]-mu*G[k-1])
                    for k in range(L,b-1):assert geq2(G[k]-mu*G[k-1])
                    ct['independent_onefactor_to_twofactor_separate_exception_payments']+=1
    for u in range(5):
        for _ in range(45):
            V=sorted(rng.choices(range(3,19),k=rng.randint(1,8)));h=sum(t-1 for t in V);W=sum(V)
            if h>=3*u+3 or u==0:
                I=infinite_ones([2]*u+V,W);assert I[W]-I[W-1]<=I[W-1]-I[W-2]
                ct['independent_small_u_exact_infinite_padding_boundary_nondecrease']+=1
            else:
                assert W<=21<32;ct['independent_small_u_complement_OLD_weight32_guards']+=1
            for alpha in {1,2,u+h+2}:host(alpha,u,V,ct)
    for _ in range(160):
        V=sorted(rng.choices(range(3,31),k=rng.randint(1,9)));h=sum(t-1 for t in V);u=rng.randint(0,2*h)
        host(rng.randint(1,3*u+2*h+1),u,V,ct)
    deps=['sharp_previous_ordinary_LC_verification.json','universal_late_C_first_crossing_verification.json',
      'physical_boundary_golden_C_verification.json','previous_boundary_C_verification.json',
      'general_one_jump_analytic_C_verification.json','quantitative_tilt_one_jump_strong_verification.json',
      'hereditary_strong_late_C_verification.json','multitail_binary_prefix_finite_principle_verification.json',
      'golden_tail_large_shift_C_verification.json','ordinary_golden_growth_source_verification.json']
    for name in deps:
        dep=json.loads((SOURCE/name).read_text())
        assert dep['status'].startswith('PASS'),name
        for f,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/f).read_bytes()).hexdigest()==digest,f
    files=['universal_physical_boundary_C_proof.tex','UniversalPhysicalBoundaryC.lean','UniversalPhysicalBoundaryC.log',
      'audit_universal_physical_boundary_C.py','audit_universal_physical_boundary_C.json',
      'verify_universal_physical_boundary_C.py']+deps
    def fp(f):return ROOT/f if (ROOT/f).exists() else SOURCE/f
    out=dict(status='PASS_UNIVERSAL_ACTUAL_C_FROM_PHYSICAL_W_AND_LATE_OWNER_SOURCE_BRIDGE',
      new_scoped_reports=12,kernels=kernels(),QA=qa['counts'],independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),
      new_finite_entrance_certificates=0,
      theorem='PROVED ALLactualnormalized1alpha2uV,ALLu/h/alpha/caps/counts: ENTIREC forEVERYcurrentN>=W andEVERYshiftR>=3. UniversalW+1tailupgradedtoPHYSICALWwithoutparameterrestriction.',
      maximal_margin='PROVED normalizedtiltGmargin2-lambda ->2-mu,mu=a*lambda>=1,1<=lambda<=2. EXACTFULL-rowremainder(k-1)(1-a)a^2lambda>=0. OnefactorphysicalreferenceordinaryprefixLCsuppliesmaximalmargin;normalizedrelativeDLC+twiceLRpaysactualonefactorcrossingdelta>=2at2-mu>q^2.',
      boundary_induction='PROVED firstcrossingr>=2viaone-earlierordinaryseed+q^2oldGprefix;HEREDITARYusesTWOadjacentolddratioslambda0atW,lambda1atW+1,capmax(1,lambda0,lambda1),universallate-strongGANDsharpordinaryLCfromW-1. NOTDLCatW(false). LCendpointsubtractionintegratesGmarginandaffinewindowatom1payseveryread. Oldr1delta1oddgoldenexceptionkeptSEPARATE:protectedoldGatNEWmu<phi.',
      small_counts='PROVED ALLu<=4: h>=3u+3allinfinite-paddingrowsnonincreasingatphysicalW;finitepaddingrelativeDdensitythroughmodeboundsactualedge;complementW<=21<32coveredbyOLDunbounded-paddingweight32COMPLETEC. No newfiniteentrance.',
      original_source_extension='PROVED localC-to-ScomparisonforEVERYownerj>=W_A-1,withNOoldlargebandupperboundj<=u_A+r_A+kappa_B,whenoppositenonrectangularkappa_B>=3,bothordinaryfactorsstrictlyrisingatj+1,currentreverse-source/headguards. Tailnonrecovery;coupledSretainsOLDweightedA2HEADpremise. Earlierowner/mixed/fullA2notasserted.',
      formal_scope='TWELVEcleanstandardaxiomscopedreports:maximaltiltFULLrowidentity,twolayermaximum/cap/margin,strictpositivewindowguard,ALLlarge-degreerowcentres,previousunit,smallcountOLDweight32complement,andoriginalsourcecurrentread. Naturalindex/fullrow/weighted/mode/LRproofsreused. Actualmodel/reference/word/cumulative/convolutionassembliesareWRITTEN,notend-to-endLeancompositionidealtheorem. FiniteQAONLY.',
      remaining='ALLactualCfromN>=WPROVED. GeneralearlierN<W C/fullA2/originalunamplifiedcoefficientUIOPEN;firstunresolvedFULLCnononecount6unchanged. CumulativeLCNOTcoefficientUI.',
      actual_C_current_start='W',late_C='PROVED_UNIVERSAL_FROM_W',general_original='OPEN',general_C='OPEN',general_A2='OPEN',
      sha256={f:hashlib.sha256(fp(f).read_bytes()).hexdigest() for f in files})
    (ROOT/'universal_physical_boundary_C_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('sha256','kernels')}),flush=True)
if __name__=='__main__':main()
