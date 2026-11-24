"""Complete independent diagonal grammar and positive-box full-C verification."""
from pathlib import Path
import sys,json,hashlib,re
from itertools import accumulate
from random import Random
from collections import Counter
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
NAMES=['exterior_square_tribonacci_identity','signed_third_order_majorant','full_tribonacci_minor_recurrence',
 'universal_tribonacci_previous_minor_bound','central_integer_budget_implies_relative_LC',
 'first_ternary_loss_minor_budget','second_ternary_loss_minor_budget','strict_integer_concavity_minor_budget',
 'positive_three_window_minor_budget','exact_all_padding_clamp','later_three_window_old_minor_reads','strict_mode_transition_read_guards']

def kernels():
    out={}
    for stem,ns,names in [('TernaryRichCompleteC','TernaryRichCompleteC',NAMES),
       ('TernaryRichDiagonalCertificate','TernaryRichDiagonalCertificate',['all_diagonal_integer_margins'])]:
        src=(ROOT/(stem+'.lean')).read_text();log=(ROOT/(stem+'.log')).read_text()
        assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
        assert not any(x in log for x in ('error:','warning:','sorryAx','ofReduceBool','failed'))
        assert log.count('depends on axioms:')==len(names)
        for n in names:
            m=re.search(re.escape("'"+ns+'.'+n+"'")+r' depends on axioms: \[([^]]*)\]',log);assert m,n
            ax={a.strip() for a in m.group(1).split(',') if a.strip()};assert ax<={'propext','Classical.choice','Quot.sound'}
            out[ns+'.'+n]=sorted(ax)
    return out

def box(alpha,u,r):
    F=suffix_boxes(alpha,[2]*u+[3]*r)[:alpha+2*u+3*r+1]+[0]
    return F,[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]

def main():
    data=json.loads((ROOT/'ternary_rich_diagonal_certificate_data.json').read_text())
    assert data['status']=='COMPLETE_DIAGONAL_ENTRANCE_UNDER_INDEPENDENT_RECONSTRUCTION'
    qa=json.loads((ROOT/'audit_ternary_rich_complete_C.json').read_text());assert qa['status']=='EXACT_QA_STATIONARY_THREE_FULL_C_UNDER_AUDIT'
    contexts=[];unique=set();ct=Counter();sha=hashlib.sha256()
    for u in range(4,33):
        r=2*u;clamp=r+u//2;B=(3*u+4*r)//2
        assert r+u+clamp+1==B+1
        for alpha in range(1,clamp+1):
            F,D=box(alpha,u,r);ell=D.index(max(D));assert ell<=B
            margins=[]
            for n in range(r+3,ell):
                M=D[n]**2-D[n-1]*D[n+1]-D[n];assert M>=0
                margins.append(M);unique.add(M);ct['independent_COMPLETE_diagonal_strong_minor_comparisons']+=1
            row=dict(u=u,r=r,alpha=alpha,clamp=clamp,first_mode=ell,margins=margins)
            contexts.append(row);sha.update(json.dumps(row,separators=(',',':')).encode())
            ct['independent_COMPLETE_diagonal_padding_hosts']+=1
        _,base=box(clamp,u,r)
        for alpha in {clamp+1,2*clamp+u+2}:
            _,DD=box(alpha,u,r);assert DD[:B+1]==base[:B+1] and DD.index(max(DD))==base.index(max(base))
            ct['independent_exact_ALL_larger_padding_clamp_representatives']+=1
    assert contexts==data['contexts'] and sorted(unique)==data['unique_margins']
    assert sha.hexdigest()==data['state_sha256']
    assert len(contexts)==1298 and ct['independent_COMPLETE_diagonal_strong_minor_comparisons']==93831 and len(unique)==34977
    src=(ROOT/'TernaryRichDiagonalCertificate.lean').read_text()
    parts=re.findall(r'def part\d+ : List ℤ := \[([^]]*)\]',src);assert len(parts)==117
    leanvalues=[int(x.strip()) for p in parts for x in p.split(',') if x.strip()]
    assert leanvalues==sorted(unique)
    rng=Random(20261031671);indsha=hashlib.sha256()
    for _ in range(170):
        u=rng.randint(4,32);r=rng.randint(2*u,2*u+70);alpha=rng.randint(1,3*u+3*r)
        F,D=box(alpha,u,r);ell=D.index(max(D));H=[1]
        for n in range(1,ell+2):H.append(sum(H[max(0,n-3):n]))
        R=[0,0]+[H[n]-H[n-1] for n in range(2,len(H))]
        for n in range(3,ell):
            assert D[n]<=R[n]
            if n>=r+3:assert D[n]**2-D[n-1]*D[n+1]>=D[n]
            assert D[n]**2*R[n-1]*R[n+1]>=D[n-1]*D[n+1]*R[n]**2
            ct['independent_positive_box_WHOLE_relative_tribonacci_LC']+=1
        G=list(accumulate(F));best=1
        for n in range(4,len(F)):
            k=n-3
            if G[k]*G[best-1]<G[best]*G[k-1]:best=k
            assert G[best]*D[n-1]>=G[best-1]*D[n]
            ct['independent_FULL_C_all_current_prefix_minima']+=1
            ct['independent_FULL_C_all_shift_logical_reads']+=n-3
        ct['independent_arbitrary_later_three_count_hosts']+=1
        indsha.update(json.dumps([alpha,u,r,ell,D[r+2:r+6]],separators=(',',':')).encode())
    deps=['relative_C_inheritance_verification.json','source_single_notch_verification.json',
      'mode_only_uniform_tail_closure_verification.json','general_one_jump_analytic_C_verification.json']
    for name in deps:
        dep=json.loads((SOURCE/name).read_text());assert dep['status'].startswith('PASS'),name
        for f,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/f).read_bytes()).hexdigest()==digest,f
    old=['first_missing_renewal_envelope.tex','FirstMissingRenewalEnvelope.lean','FirstMissingRenewalEnvelope.log',
      'audit_first_missing_renewal_envelope.json','second_forward_difference_source.tex',
      'sharpened_forward_derivative_centers.tex','SharpenedForwardDerivativeCenters.lean','SharpenedForwardDerivativeCenters.log',
      'universal_prefix_C_window_transfer.tex','UniversalPrefixCWindowTransfer.lean','UniversalPrefixCWindowTransfer.log']
    assert json.loads((SOURCE/'audit_first_missing_renewal_envelope.json').read_text())['status']=='PASS_FIRST_MISSING_RENEWAL_ENVELOPE'
    files=['ternary_rich_finite_entrance_complete_C_proof.tex','TernaryRichCompleteC.lean','TernaryRichCompleteC.log',
      'TernaryRichDiagonalCertificate.lean','TernaryRichDiagonalCertificate.log','build_ternary_rich_diagonal_certificate.py',
      'ternary_rich_diagonal_certificate_data.json','audit_ternary_rich_complete_C.py','audit_ternary_rich_complete_C.json',
      'verify_ternary_rich_complete_C.py']+deps+old
    def fp(f):return ROOT/f if (ROOT/f).exists() else SOURCE/f
    out=dict(status='PASS_STATIONARY_THREE_COMPLETE_C_BINARY_COUNTS_FOUR_THROUGH_THIRTY_TWO',
      new_scoped_reports=13,generic_reports=12,finite_certificate_reports=1,kernels=kernels(),QA=qa['counts'],
      independent_counts=dict(ct),complete_entrance_state_sha256=sha.hexdigest(),independent_later_state_sha256=indsha.hexdigest(),
      new_finite_entrance=dict(binary_counts=list(range(4,33)),three_count='r0=2u',padding='ALL1<=alpha<=r0+floor(u/2),lastrepALLlarger',
        contexts=1298,comparisons=93831,distinct_integer_margins=34977,kernel_chunks=117),
      theorem='PROVED FULLactualC EVERYcurrentN/EVERYshift>=3 forALL1alpha2u3r with4<=u<=32,r>=2u,alpha>=1. THREEcountandpaddingUNBOUNDED;binaryrangeEXPLICIT. No universalu>=33claim.',
      strong_heredity='PROVED forallfixedu>=4,EVERYr>=8,ALLpadding: actualpre-FIRSTDmodeintegerbudgetD_n^2-DprevDnext>=D_nfromn>=r+3isHEREDITARYunderappend3. TWOnewentrancespaidANALYTICALLYbyexactlosses1,r+1,(r^2+3r+6)/2andALL-ntribonacci-minorbound;laterpositive3windowusesFULLcrossidentitywithpositiveinputguard;OLDmode-transitionstrictconcavityusesactualsoleflat4. No oldLCafterFIRSTmodeassumed.',
      renewal_transfer='PROVED WHOLEactualD/H3-D relativeLCthroughFIRSTmode: reference|minor|<=previousfromactualcentre5viaFULLthird-orderexterior-square+signedmajorantinduction;strongactualminor>=centralandcentraldominationfromFULLsecondsourcepayrelativeLC. Exactprefixbeforefirstloss+boundaryretained. COMPLETEH3renewalC/normalizedtilt/twiceLRthenpayALLactualCshifts;laterDnonincreasingautomatic.',
      long_last_jump='PROVED samequalifyingbinary-threeblock+ANYsortedL>=3withL+4>=floor((3u+4r)/2)hasFULLCbyconditionalprefix/oldFIRSTDmode. ALLr/padding/Lunbounded. DoesNOTclaimALLlargejumpswithouttheexplicitthreshold.',
      coupled='OrdinaryproductcoefficienttiltUIvsANYoppositeandALLdepthguardedBOTH-FrisingC-to-Snonrecovery;OLDweightedA2head/physical/currentguardsretained. No generaloriginalUIinference.',
      formal_scope='TWELVEnewcleanstandardaxiomgenericreports,includingFULLnatural-indextribonacci-minorrecurrenceanduniformprevious-coefficientbound,relativeLCpayment,TWOanalyticentrances,positive3windowcrosspayment,strictconcavityandread/paddingguards. ONEadditionalaggregateordinaryLean-kernelreportchecksALL34977diagonalintegermarginsin117chunks. Actualword/Fibonacci/reference/loss/positive-support/single-flat/mode/signed-splice/cumulative/fullr-inductionandCassemblyWRITTENwithregisteredinputs. IndependentPOSITIVEboxrebuildcoversALL1298finitehosts/93831minors,notrandom. Notend-to-endLeancompositiondatatype.',
      remaining='Generalu>=33ternary-richdiagonalr=2uUNPROVED;u<=3andothernon-dominantmulti-threeFULLCnotclaimedhere. GeneralC/fullA2/originalunamplifiedcoefficientUIOPEN;totalnononefirstunresolved6unchanged. CDFLCNOTsubstitutedforcoefficientUI.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',
      sha256={f:hashlib.sha256(fp(f).read_bytes()).hexdigest() for f in files})
    (ROOT/'ternary_rich_complete_C_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('sha256','kernels')}),flush=True)
if __name__=='__main__':main()
