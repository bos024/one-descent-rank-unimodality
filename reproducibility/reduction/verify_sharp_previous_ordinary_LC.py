"""Independent positive-box audit of the sharp universal one-earlier ordinary LC theorem."""
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
NAMES=['one_earlier_crossing_guards','head_plus_tail_dominance','reference_previous_ordinary_minor',
 'nonincreasing_positive_slopes_LC','binary_cumulative_first_defect_seed','local_window_LC_read_guards',
 'sharp_triple_minor_identity','sharp_minor_negative_all_capacities','sharp_triple_strict_growth','binary_reference_CDF_minor']
def kernels():
    src=(ROOT/'SharpPreviousOrdinary.lean').read_text();log=(ROOT/'SharpPreviousOrdinary.log').read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(x in log for x in ('error:','warning:','sorryAx','ofReduceBool','failed'))
    assert log.count('depends on axioms:')==10
    out={}
    for n in NAMES:
        m=re.search(re.escape("'SharpPreviousOrdinary."+n+"'")+r' depends on axioms: \[([^]]*)\]',log);assert m,n
        ax={a.strip() for a in m.group(1).split(',') if a.strip()};assert ax<={'propext','Classical.choice','Quot.sound'}
        out[n]=sorted(ax)
    return out
def box(alpha,u,V):
    W=sum(V);return suffix_boxes(alpha,[2]*u+V)[:alpha+2*u+W+1]+[0]
def main():
    qa=json.loads((ROOT/'audit_sharp_previous_ordinary_LC.json').read_text())
    assert qa['status']=='EXACT_QA_SHARP_W_MINUS_ONE_ORDINARY_LC_UNDER_AUDIT' and not qa['counterexamples']
    rng=Random(20261031459);ct=Counter();sha=hashlib.sha256()
    for u in range(41):
        for alpha in {1,2,u+3,2*u+5}:
            F=box(alpha,u,[]);G=list(accumulate(F))
            for n in range(1,len(G)-1):
                assert G[n]**2>=G[n-1]*G[n+1];ct['independent_BINARY_GLOBAL_forward_CDF_LC_minors']+=1
    for _ in range(170):
        u=rng.randint(5,65);r=rng.randint(1,max(1,u//3));h=rng.randint(2*r,u);ds=[2]*r
        for j in range(h-2*r):ds[rng.randrange(r)]+=1
        V0=sorted(d+1 for d in ds);a=sum(V0);L=u+r+1
        low=max(V0[-1],u-h+3);t=rng.randint(low,max(low,2*u-1));V=V0+[t];b=a+t
        RR=reference(V0,L);RG=list(accumulate(RR))
        for alpha in {1,2,2*u+h+3}:
            V=V0+[t]
            F=box(alpha,u,V0);G=list(accumulate(F));NF=box(alpha,u,V)
            D=[0,0]+[max(0,NF[n]-NF[n-1]) for n in range(2,len(NF))]
            A,B=D[b-1:b+1]
            if B>A>0:
                assert sign((F[a-1],-F[a-2]))>0 and sign((-F[b-1],F[b-2]))>0
                assert B*F[b-2]<A*F[b-1] and G[:L+1]==RG[:L+1]
                assert A*G[L]-B*G[L-1]>A*G[a-2]-B*G[a-3]
                assert A*G[b-2]-B*G[b-3]>A*G[a-2]-B*G[a-3]
                assert A*NF[b-1]-B*NF[b-2]==(A*G[b-2]-B*G[b-3])-(A*G[a-2]-B*G[a-3])>0
                ct['independent_one_earlier_first_crossing_exact_seed_payments']+=1
            for n in range(b-1,len(NF)-1):
                assert NF[n]**2>=NF[n-1]*NF[n+1];ct['independent_first_crossing_ENTIRE_W_minus_one_tail']+=1
            V=V0+[t]
            for step in range(2):
                V=V+[rng.randint(V[-1],max(V[-1],2*u))]
                SF=box(alpha,u,V);W=sum(V)
                for n in range(W-1,len(SF)-1):
                    assert SF[n]**2>=SF[n-1]*SF[n+1]
                    ct['independent_arbitrary_suffix_ENTIRE_W_minus_one_tail']+=1
            sha.update(json.dumps([alpha,u,V0,t,V,SF[sum(V)-2:sum(V)+2]],separators=(',',':')).encode())
    fib=[0,1]
    for _ in range(220):fib.append(sum(fib[-2:]))
    witnesses=[]
    for T in range(4,100):
        for alpha in {1,3,2*T+1}:
            F=box(alpha,T,[3,T]);W=T+3;triple=F[T:T+3]
            assert triple==[2*fib[T+1]-2,2*fib[T+2]-3,2*fib[T+3]-4]
            minor=triple[1]**2-triple[0]*triple[2]
            assert minor==1-4*fib[T-2]+4*(-1)**(T+1)<0
            assert triple[0]<triple[1]<triple[2] and F.index(max(F))>T+1
            for n in range(W-1,len(F)-1):assert F[n]**2>=F[n-1]*F[n+1]
            ct['independent_positive_box_SHARP_family_exact_triples']+=1
            if T==5 and alpha==1:witnesses.append(dict(alpha=alpha,u=T,V=[3,T],W=W,centre=T+1,triple=triple,minor=minor))
    deps=['universal_late_C_first_crossing_verification.json','binary_ordinary_tail_and_one_jump_C_verification.json',
          'reference_ordinary_golden_prefix_verification.json','surplus_ordinary_tail_LC_verification.json',
          'quantitative_tilt_one_jump_strong_verification.json']
    for name in deps:
        dep=json.loads((SOURCE/name).read_text())
        for f,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/f).read_bytes()).hexdigest()==digest,f
    files=['sharp_previous_ordinary_LC_proof.tex','SharpPreviousOrdinary.lean','SharpPreviousOrdinary.log',
           'audit_sharp_previous_ordinary_LC.py','audit_sharp_previous_ordinary_LC.json',
           'verify_sharp_previous_ordinary_LC.py']+deps
    def fp(f):return ROOT/f if (ROOT/f).exists() else SOURCE/f
    out=dict(status='PASS_SHARP_UNIVERSAL_DEFICIT_ORDINARY_COEFFICIENT_LC_FROM_W_MINUS_ONE',
      new_scoped_reports=10,kernels=kernels(),QA=qa['counts'],independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),
      new_finite_entrance_certificates=0,
      theorem='PROVED ALLactualnormalized1alpha2uV withu>=5,h>u,ALLpadding/caps/counts: ENTIREordinaryFcoefficientLCatEVERYcentreN>=W-1. UniversalstartW-1isSHARP. Ordinarycoefficienttheorem,notCDFLC/originalcoreUI.',
      first_crossing='PROVED firstcrossingdelta>=2byshiftingtwoENDPOINTgoldenboundsONErank:oldlefta-1>=2protectedreference,oldrightb-1>=u+r0+2actualceiling. AddpositiveH_(a-1)toFULLalternatingtaildominance,payexactordinarywindowseedatb-1. delta1protectedminorEXACTR_W-referenceA>=0. Nongrowingentriesbyconcavity/tailLC,notDLCatW.',
      onefactor_and_suffix='PROVED binaryFORWARDCDFGLOBALordinaryLC bycumFibCassini/firstdefectseed+ENTIREordinarybinarytailLC/cumulativeintegration. OnefactorprefixF_n=Gbinary_(n-1)throughcapacityL payscentreL-1. EverylaterlegalappendinheritsordinaryLCfromFINALW-1byfulluniformwindowconvolutionwitholdFtruncatedbelowoldW-2.',
      sharpness='PROVED UNBOUNDEDACTUALfamily1alpha2^T(3,T),ALLT>=4/alpha>=1,atcentreW-2=T+1: triple(2Fib(T+1)-2,2Fib(T+2)-3,2Fib(T+3)-4),minor1-4Fib(T-2)+4(-1)^(T+1)<0. ALLT>=5meettheoremclassu>=5,h>u. Strictlyrisingtriple,beforeFIRSTordinarymode. DoesNOTrefuteUI/C.',
      sharpness_witnesses=witnesses,
      formal_scope='TENnewcleanstandardaxiomreports;allread/convolutionguards,head-plus-taildominance,protectedpreviousreferenceordinaryminor,concavity/cumulativefirstdefect,EXACTsharpminoridentityandNat.fib-basedALLTnegativity. Actualreference/binaryCDF/word/modeassembliesWRITTEN,notend-to-endLeanactualcompositiontheorem. FiniteQAONLY,no finite premise.',
      remaining='UniversalLATECremainsPROVED.GeneralphysicalWboundaryC/earlierC/fullA2/originalunamplifiedcoefficientUIOPEN;firstunresolvedFULLCcount6unchanged.',
      late_C='PROVED_UNIVERSAL',general_original='OPEN',general_C='OPEN',general_A2='OPEN',
      sha256={f:hashlib.sha256(fp(f).read_bytes()).hexdigest() for f in files})
    (ROOT/'sharp_previous_ordinary_LC_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('sha256','kernels')}),flush=True)
if __name__=='__main__':main()

