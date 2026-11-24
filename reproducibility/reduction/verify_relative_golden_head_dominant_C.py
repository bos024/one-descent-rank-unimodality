"""Independent ordered/unordered box/reference checks of unbounded closure."""
from pathlib import Path
import sys,json,hashlib,re
from itertools import accumulate
from fractions import Fraction as Frac
from random import Random
from collections import Counter
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
from verify_physical_boundary_golden_C import reference
from audit_arbitrary_Fibonacci_tail_late_C import sign,sub,mul,power
Q=(-1,1);C=power(Q,6)
NAMES=['sixth_power_atom_budgets','nonempty_head_interval_bound','complete_quantitative_head_tail_window',
 'all_dominant_reference_read_guards','dominant_deficit_and_small_count_mode',
 'dominant_surplus_actual_read_guards','strict_reference_tail_payment','all_current_dominant_assembly']

def kernels():
    src=(ROOT/'RelativeGoldenHeadDominantC.lean').read_text();log=(ROOT/'RelativeGoldenHeadDominantC.log').read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(x in log for x in ('error:','warning:','sorryAx','ofReduceBool','failed'))
    assert log.count('depends on axioms:')==8
    out={}
    for n in NAMES:
        m=re.search(re.escape("'RelativeGoldenHeadDominantC."+n+"'")+r' depends on axioms: \[([^]]*)\]',log);assert m,n
        ax={a.strip() for a in m.group(1).split(',') if a.strip()};assert ax<={'propext','Classical.choice','Quot.sound'}
        out[n]=sorted(ax)
    return out

def main():
    qa=json.loads((ROOT/'audit_relative_golden_head_dominant_C.json').read_text())
    assert qa['status']=='EXACT_QA_UNIVERSAL_RELATIVE_GOLDEN_HEAD_AND_DOMINANT_C_UNDER_AUDIT'
    rng=Random(20261031561);ct=Counter();sha=hashlib.sha256()
    for _ in range(150):
        V=rng.choices(range(3,25),k=rng.randint(1,12));a=sum(V);R=reference(V,a+1);rho=(R[a],-R[a-1])
        for j in range(2,a+1):
            assert sign(sub((R[j],-R[j-1]),mul(C,rho)))>=0
            ct['independent_ARBITRARY_order_ALL_relative_golden_head_reads']+=1
        t=rng.randint(3,a+12);N=a+t+1;RR=reference(V+[t],N);G=list(accumulate(RR))
        d=[0,0]+[RR[n]-RR[n-1] for n in range(2,len(RR))]
        for n in range(max(t+3,a+8),N+1):
            assert sign((-d[n],d[n-1]))>0
            for k in range(1,n-2):
                assert G[k]*d[n-1]>=G[k-1]*d[n];ct['independent_unconditional_EARLIER_reference_C_all_shift_reads']+=1
            ct['independent_unconditional_EARLIER_reference_golden_D_edges']+=1
    def full(F,D):
        G=list(accumulate(F));best=1
        for n in range(4,len(F)):
            k=n-3
            if G[k]*G[best-1]<G[best]*G[k-1]:best=k
            assert G[best]*D[n-1]>=G[best-1]*D[n]
            ct['independent_FULL_actual_C_all_current_prefix_minima']+=1
            ct['independent_FULL_actual_C_all_shift_logical_reads']+=n-3
    def box(alpha,u,V):
        F=suffix_boxes(alpha,[2]*u+V)[:alpha+2*u+sum(V)+1]+[0]
        return F,list(accumulate(F)),[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
    seeds=[]
    for _ in range(25):
        r=rng.randint(2,6);V=sorted(rng.choices(range(3,7),k=r))
        if sum(V)<=32:seeds.append(V)
    for V in seeds:
        for step in range(2):
            a=sum(V);r=len(V);h=a-r;t=2*a+rng.randint(0,3);W=a+t
            for u in {0,5,max(0,h-1),h,2*a}:
                for alpha in {1,u+a+3}:
                    OF,OG,od=box(alpha,u,V);F,G,D=box(alpha,u,V+[t]);full(F,D)
                    ell=od.index(max(od));assert 2*ell<=3*u+a+r+1
                    if u<h or u+r<=5:assert ell<=t+4
                    else:
                        L=u+r+1
                        for n in range(max(t+5,L+2),min(ell,W-1)+1):
                            A,B=D[n-1:n+1]
                            if not A or B<=A:continue
                            assert B*OF[n-2]<A*OF[n-1]
                            mu=Frac(B,A)
                            for k in range(1,n-1):
                                v=OG[k]-mu*OG[k-1]
                                assert sign((v.numerator-2*v.denominator,v.denominator))>=0
                                ct['independent_dominant_surplus_ENTIRE_old_G_prefix_margins']+=1
                            ct['independent_dominant_strict_actual_window_transfers']+=1
                    ct['independent_dominant_uniform_actual_hosts']+=1
                    sha.update(json.dumps([alpha,u,V,t,ell,D[W-1:W+1]],separators=(',',':')).encode())
            V=V+[t]
    # Explicit many-factor sequence, without changing the arbitrary-u theorem's scope.
    V=[3,4]
    for _ in range(4):V.append(2*sum(V))
    for u in {0,5,20,80}:
        F,G,D=box(3,u,V);full(F,D);ct['independent_SIX_nonbinary_factor_dominant_hosts']+=1
    RR=reference([3,4],7);rho=(RR[7],-RR[6]);gap=(RR[5],-RR[4])
    assert sign(sub(gap,mul(power(Q,2),rho)))<0
    control=dict(V=[3,4],rank=5,H=list(gap),terminal=list(rho),failed_stronger_constant='q^2',actual_C_counter=False)
    deps=['two_nonbinary_complete_C_verification.json','universal_physical_boundary_C_verification.json',
      'reference_ordinary_golden_prefix_verification.json','hereditary_strong_late_C_verification.json',
      'previous_boundary_C_verification.json','multitail_binary_prefix_finite_principle_verification.json',
      'universal_late_C_first_crossing_verification.json']
    for name in deps:
        dep=json.loads((SOURCE/name).read_text());assert dep['status'].startswith('PASS'),name
        for f,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/f).read_bytes()).hexdigest()==digest,f
    files=['relative_golden_head_dominant_C_proof.tex','RelativeGoldenHeadDominantC.lean','RelativeGoldenHeadDominantC.log',
      'audit_relative_golden_head_dominant_C.py','audit_relative_golden_head_dominant_C.json',
      'verify_relative_golden_head_dominant_C.py']+deps
    def fp(f):return ROOT/f if (ROOT/f).exists() else SOURCE/f
    out=dict(status='PASS_UNIVERSAL_RELATIVE_GOLDEN_HEAD_AND_UNBOUNDED_DOMINANT_COMPLETE_C_CLOSURE',
      new_scoped_reports=8,kernels=kernels(),QA=qa['counts'],independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),
      new_finite_entrance_certificates=0,
      universal_head='PROVED EVERYarbitrary-ORDERnonemptyreferenceV,ALL2<=j<=W: H_j>=q^6*H_W>0,H_j=R_j-phiRprev. TerminalH_W=rho=prod q(1-psi^t) contractsunderEVERYappendandlies(0,1). FULLquantitativehead-plus-alternating-tailwindowinduction,constantINDEPENDENTallweights/counts/caps.',
      unconditional_reference_resource='PROVED forANYoldreferenceweightaandANYappendt>=3: EVERYcurrent max(t+3,a+8)<=N<=a+t+1hasSTRICTgoldenDgapandALLCshifts,NOoldCpremise. EXACTgapH_(N-t-1)-H_(N-1),head>=q6rhoandrighttail<=q7rho. GeneralreferencefullCstillOPENoutsideprovedregions.',
      uniform_full_C_inheritance='PROVED iffixedsortednonbinaryVhasFULLactualCforallbinaryu/paddingalpha,EVERYlegalappendt>=2sumVpreservesthatUNIFORMfullC. OldreferencefullCbyfiniteprefix;newreferencefullCbyearliergoldengap+prefix+oldW-1tail. Deficitu<hORu+r<=5modeell<=t+4;surplususesprotectednewreferenceCbelowfirstlossandoldordinaryLCfromu+r+1aboveit. BOTHendgoldenbounds+ALLGq2prefixintegration+affineatom1payresidual. Nobinarycount/paddingdependenceindominancecondition.',
      arbitrary_length_family='PROVED startwithANYuniformfullCtailseed,thenARBITRARILY MANYlegalappends t_j>=2SUMpreviousnonbinarycapacities: ALLresulting1alpha2uVhaveFULLC,ALLalpha/u/ranks/shifts. SeedsincludeTWOarbitrarynonbinaryfactorsandANYoldweight<=32tail. Nonbinarycount/capacities/binarycount/paddingALLUNBOUNDED.',
      coupled='OrdinaryproductcoefficienttiltUIagainstANYoppositeandALLdepthBOTH-FrisingC-to-Snonrecoverywithcurrent/physicalguards/OLDweightedA2headretained. FullA2/originalUINOTasserted.',
      stronger_head_control=control,
      formal_scope='EIGHTnewcleanstandardaxiomreportsincludingFULLquantitativeinterval-windowtheorem,ALL-qbudgets,ALLdominant/actualreads,ALLdeficit/smallcountmodeexclusion,strictgapandcompleteNat-indexassembly. Actualreference/CI/rho/word/Fibonacci/cumulative/convolution/coupledidentificationsandtail-wordinductionWRITTENwithregisteredinputs. FiniteQAONLY,no finite premise;notend-to-endLeancompositiondatatype.',
      remaining='Generalnondominant>=3nonbinaryFULLC/fullA2/originalunamplifiedcoefficientUIOPEN. FirstunresolvedTOTALnononecount6unchanged.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',
      sha256={f:hashlib.sha256(fp(f).read_bytes()).hexdigest() for f in files})
    (ROOT/'relative_golden_head_dominant_C_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('sha256','kernels')}),flush=True)
if __name__=='__main__':main()
