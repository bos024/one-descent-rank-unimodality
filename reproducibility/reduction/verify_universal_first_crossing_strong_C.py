"""Independent actual suffix-box verification of universal late C; no sampled logical premises."""
from pathlib import Path
import sys,json,re,hashlib
from itertools import accumulate
from random import Random
from collections import Counter
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
from verify_physical_boundary_golden_C import reference
from audit_arbitrary_Fibonacci_tail_late_C import sign
NAMES=['crossing_read_guards','golden_endpoint_cross','strict_subtracted_window_ratio',
 'full_alternating_partial_margin','reference_residual_dominance','full_cumulative_residual_propagation',
 'exact_ordinary_window_residual','ordinary_seed_gives_LC','first_strict_crossing']
def kernels():
    src=(ROOT/'UniversalLateCFirstCrossing.lean').read_text();log=(ROOT/'UniversalLateCFirstCrossing.log').read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(x in log for x in ('error:','warning:','sorryAx','ofReduceBool','failed'))
    assert log.count('depends on axioms:')==9
    out={}
    for n in NAMES:
        m=re.search(re.escape("'UniversalLateCFirstCrossing."+n+"'")+r' depends on axioms: \[([^]]*)\]',log);assert m,n
        ax={a.strip() for a in m.group(1).split(',') if a.strip()};assert ax<={'propext','Classical.choice','Quot.sound'}
        out[n]=sorted(ax)
    return out
def box(alpha,u,V):
    W=sum(V)
    return suffix_boxes(alpha,[2]*u+V)[:alpha+2*u+W+1]+[0]
def check(F,u,V,ct):
    W=sum(V);h=W-len(V);G=list(accumulate(F));D=[0,0]+[max(0,F[j]-F[j-1]) for j in range(2,len(F))]
    best=1
    for N in range(4,len(F)):
        k=N-3
        if G[k]*G[best-1]<G[best]*G[k-1]:best=k
        if N>=W+1:
            assert G[best]*D[N-1]>=G[best-1]*D[N]
            ct['independent_ENTIRE_universal_late_C_minima']+=1
    if u>=5 and h>u:
        for n in range(W,len(F)-1):
            assert F[n]**2>=F[n-1]*F[n+1];ct['independent_deficit_family_ENTIRE_ordinary_LC_tail_from_W']+=1
        A,B=D[W:W+2]
        if B>A>0:
            for k in range(1,W+1):
                assert sign((A*G[k]-B*G[k-1]-2*A,A))>=0
                ct['independent_UNIVERSAL_deficit_strong_G_prefix_reads']+=1
    ct['independent_actual_hosts']+=1
    return G,D
def main():
    qa=json.loads((ROOT/'audit_universal_first_crossing_strong_C.json').read_text())
    assert qa['status']=='EXACT_QA_UNIVERSAL_FIRST_CROSSING_STRONG_LATE_C_UNDER_AUDIT'
    rng=Random(20261031431);ct=Counter();sha=hashlib.sha256();profiles=[]
    for u in range(5,45):
        for cap in {3,min(8,u+1),u+1}:
            V=[cap]*max(1,u//(cap-1));h=sum(t-1 for t in V)
            if h<=u:profiles.append((u,V))
    for _ in range(60):
        u=rng.randint(5,80);r=rng.randint(1,max(1,u//3));h=rng.randint(2*r,u);ds=[2]*r
        for j in range(h-2*r):ds[rng.randrange(r)]+=1
        profiles.append((u,sorted(d+1 for d in ds)))
    for u,V0 in profiles:
        a=sum(V0);h0=a-len(V0);L=u+len(V0)+1
        t=rng.randint(max(V0[-1],u-h0+2),max(max(V0[-1],u-h0+2),2*u-1));b=a+t
        R=reference(V0,b+1);RG=list(accumulate(R))
        for alpha in {1,2,2*u+h0+2}:
            F=box(alpha,u,V0);G=list(accumulate(F))
            for n in range(L,len(F)-1):
                assert F[n]**2>=F[n-1]*F[n+1];ct['independent_LOOSENED_surplus_LC_including_low_u']+=1
            V=V0+[t];NF=box(alpha,u,V);NG,ND=check(NF,u,V,ct);A,B=ND[b:b+2]
            if B>A>0:
                assert sign((F[a],-F[a-1]))>0 and sign((-F[b],F[b-1]))>0
                assert B*F[b-1]<A*F[b]
                assert G[:L+1]==RG[:L+1]
                assert A*RG[L]-B*RG[L-1]>A*RG[a-1]-B*RG[a-2]
                assert A*G[b-1]-B*G[b-2]>A*G[a-1]-B*G[a-2]
                assert A*NF[b]-B*NF[b-1]==(A*G[b-1]-B*G[b-2])-(A*G[a-1]-B*G[a-2])>0
                ct['independent_COMPLETE_first_crossing_ordinary_window_payments']+=1
                if u<16:ct['independent_first_crossings_below_analytic_quotient_cutoff']+=1
            for step in range(2):
                V=V+[rng.randint(V[-1],max(V[-1],2*u))]
                NF=box(alpha,u,V);check(NF,u,V,ct)
            sha.update(json.dumps([alpha,u,V0,t,V],separators=(',',':')).encode())
    # Entire random final words, including all old and new proof branches.
    for _ in range(500):
        V=sorted(rng.choices(range(3,30),k=rng.randint(1,10)));h=sum(t-1 for t in V);u=rng.randint(0,2*h)
        alpha=rng.randint(1,max(2,u+h))
        F=box(alpha,u,V);check(F,u,V,ct)
        ct['independent_random_final_words']+=1
    witness=qa['new_first_crossing_witness'];F=box(witness['alpha'],witness['u'],witness['V'])
    G,D=check(F,witness['u'],witness['V'],ct);assert D[witness['newW']:witness['newW']+2]==witness['pair']
    deps=['surplus_ordinary_tail_LC_verification.json','degree_boundary_CI_entrance_verification.json',
          'infinite_padding_full_deficit_LC_verification.json','automatic_late_C_cones_verification.json',
          'reference_ordinary_golden_prefix_verification.json','ordinary_golden_growth_source_verification.json',
          'hereditary_strong_late_C_verification.json','quantitative_tilt_one_jump_strong_verification.json',
          'two_factor_complete_entrance_verification.json','golden_tail_large_shift_C_verification.json']
    for name in deps:
        dep=json.loads((SOURCE/name).read_text())
        for f,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/f).read_bytes()).hexdigest()==digest,f
    # Explicitly verify the full old low-u quotient scope used to remove cutoff16.
    degree=json.loads((SOURCE/'degree_boundary_CI_entrance_verification.json').read_text())
    assert 'EVERY CI quotient' in degree['quotient'] and 'positive global LC' in degree['quotient']
    files=['universal_late_C_first_crossing_proof.tex','surplus_ordinary_tail_LC_guard_refinement.tex',
           'UniversalLateCFirstCrossing.lean','UniversalLateCFirstCrossing.log',
           'audit_universal_first_crossing_strong_C.py','audit_universal_first_crossing_strong_C.json',
           'verify_universal_first_crossing_strong_C.py']+deps
    def fp(f):return ROOT/f if (ROOT/f).exists() else SOURCE/f
    out=dict(status='PASS_UNIVERSAL_ACTUAL_ALL_PADDING_ALL_SHIFT_LATE_C_BY_FIRST_CROSSING',
      new_scoped_reports=9,kernels=kernels(),state_sha256=qa['state_sha256'],QA=qa['counts'],
      independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),new_finite_entrance_certificates=0,
      theorem='PROVED EVERYactualnormalized1alpha2uV,nonemptyV>=3,ALLbinaryu>=0/taildegrees/counts/caps/paddingalpha>=1: EVERYCshiftR>=3 atEVERYcurrentN>=W+1. GENERALACTUALLATE-CENTRANCENOWCLOSED. No countcone,capacity/densityrecord/first-crossing residual. PurebinaryarmsusetheirOLDcompleteC.',
      surplus_guard_refinement='PROVED ordinaryFLCfromu+r+1 atALLu>=h withu+r>=6. Earliercutoff16ONLYinvokedanalyticordinaryquotientLC;OLDdegreeboundarycertificateALREADYPROVESfullordinaryJLCatALLu=h incl175lowucontexts,OLDsurpluscoversu>h. NewscalarproofneedsONLYw>=6. OLDcertificatesREUSED,notrecounted,no newfiniteentrance.',
      first_crossing='PROVED firstprefixdegree>u: nonemptyoldsurplusprefixhasordinaryLCfromL=u+r0+1 andPROTECTEDGthroughL. LEFTordinaryendpointatoldWgrowsoverphi,RIGHTatnewWbelowphi,soNEWwindowratio<lastordinaryratio<phi. ThisextendsALLoldGadditivemargins;rankzero/t>=3paysNEWstrongprefix.',
      ordinary_seed='PROVED MISSINGordinarywindowseedbyREFERENCEGAPDOMINANCE: allreferenceGphi-residualsafteroldWstrictlydominateatoldW-1,viaFULLalternatingpartialsum>=q²lastgap. ProtectedprefixcarriesdominancetoactualL;nonnegativeordinaryresidualspropagatetonewW-1. ExactwindowdifferencegivesFnewW-muFnewprev>0. NOactualdensityrecord/relativeLChypothesisneeded.',
      assembly='EmptyoldprefixusesOLDallonefactorstrongentrance;ARBITRARYlaterlegalsuffixesinheritbyOLDhereditarytheorem. u<=4usesOLDsmallbinarythrough8,h<=uusesOLDcomplete lateC. Allclipped/flat/pre-first-mode/post-ordinary-modeguardsexplicit. Universalpre-modeDLCintegratesseedtoALLlatercurrents.',
      ordinary_deficit_corollary='PROVED ALLu>=5,h>u: ordinaryactualcoefficientLCatEVERYcentreN>=W. Growingentriesbynewstrongentrance;nonincreasingpositiveentriesbyconcavityandordinarytailLC. ThisdoesNOTclaimphysicalWordinaryLCwhenh<=u.',
      formal_scope='NINEnewcleanstandardaxiomscopedreports;FULLfirst-crossingListinduction,ALLreadguards,strictendpointsubtraction,FULLalternatingpartialsuminduction,referencegapdominance,fullresidualintegration,exactordinarywindow/LCseedalgebra. Actualword/root/source/protectedprefix/mode/sequenceassemblyWRITTEN,notend-to-endLeancompositiontheorem. NewfinitehostsonlyQA;no newfinitepremise.',
      remaining='GENERALFULLCATEARLIERRANKSN<=W,shorterphysicalWboundaryshifts,fullA2andORIGINALunamplifiedcoefficientUIremainOPEN. DensityrecorduniversalassertionstillOPENbutUNNECESSARYforuniversalLATEC. FirstunresolvedFULLCnononecount6unchanged; no originalnumericalboundupgrade.',
      late_C='PROVED_UNIVERSAL',general_original='OPEN',general_C='OPEN',general_A2='OPEN',
      new_coverage_witness=witness,sha256={f:hashlib.sha256(fp(f).read_bytes()).hexdigest() for f in files})
    (ROOT/'universal_late_C_first_crossing_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('sha256','kernels')}),flush=True)
if __name__=='__main__':main()

