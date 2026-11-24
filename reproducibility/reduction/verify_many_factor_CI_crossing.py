"""Independent THREE-profile coverage, positive-box reads, and seventeen new kernels."""
from pathlib import Path
from fractions import Fraction
from math import comb
from random import Random
from collections import Counter
import hashlib,json,re,sys
from verify_double_subdegree_CI_entrance import multiplicities
from verify_subdegree_CI_entrance import suffix_boxes
from verify_divided_CI_surplus_three_primitive import kernel
from probe_divided_CI_positive_primitive import divided
from audit_joint_structure import fastconv
from audit_arbitrary_Fibonacci_tail_late_C import add,sub,mul,power,sign
ROOT=Path(__file__).resolve().parent
Q=(-1,1);Z=(0,0)
UNSCALED=['uniform_rank_factor','unscaled_interior_scalar','penultimate_lower_factor',
 'penultimate_two_payments','penultimate_coefficient_lower','unscaled_zero_row',
 'fast_source_raw_minor','fast_source_positive_part_LC','binomial_growth_pays_fast_source']
MANY=['interior_unscaled_five_fourths','interior_numerator_zero_row','stronger_interval_norm_constants',
 'many_factor_nonlong_geometry','fast_window_only_three_integer_pairs','many_factor_perturbed_junction',
 'discarded_primitive_prefix_is_absent']

def determinant(a,n):return sub(mul(a[n],a[n]),mul(a[n-1],a[n+1]))

def main():
    qa=json.loads((ROOT/'audit_many_factor_CI_crossing.json').read_text(encoding='utf8'))
    uq=json.loads((ROOT/'probe_unscaled_head_and_fast_source.json').read_text(encoding='utf8'))
    assert qa['status']=='EXACT_QA_MANY_FACTOR_CROSSING_UNDER_PROOF_AUDIT'
    assert qa['state_sha256']=='15b3317f44bf21cdac64d7c670da771532c4931e3954d285196284a770cb16c3'
    assert uq['state_sha256']=='4c41aef8be58b03c38be67d25a70142d3fcea8c989a72159e3a5d8e52f41dd98' and not uq['counters']
    produced={(r['u'],tuple(r['V'])):r for r in qa['complete_exception_profiles']};keys=set();integers=set();ct=Counter();sha=hashlib.sha256()
    for u,delta in ((15,3),(16,3),(20,4)):
        for V in multiplicities(u+delta,u+delta):
            if len(V)<6 or min(V)-1<delta:continue
            key=(u,tuple(V));assert key not in keys;keys.add(key);row=produced[key];h=u+delta;W=sum(V)
            assert row['h']==h and row['padding_clamp']==(u+h)//2
            assert len(row['hosts'])==row['padding_clamp']+1
            for alpha,host in enumerate(row['hosts'],1):
                F=suffix_boxes(alpha,[2]*u+V);g=[max(0,F[n]-F[n-1]) for n in range(W,len(F))];M=g.index(max(g));margins=[]
                for n in range(1,M):
                    z=g[n]**2-g[n-1]*g[n+1];assert z>=0;integers.add(z);margins.append(z);ct['complete_exception_minors']+=1
                assert alpha==host['alpha'] and M==host['first_tail_mode'] and margins==host['margins'];ct['complete_exception_hosts']+=1
                sha.update(json.dumps([u,V,alpha,F],separators=(',',':')).encode())
    assert keys==set(produced) and len(keys)==3 and ct['complete_exception_hosts']==58 and ct['complete_exception_minors']==770
    assert sorted(integers)==qa['integer_margins'] and len(integers)==449
    source=(ROOT/'ManyFactorCrossingCertificate.lean').read_text(encoding='utf8')
    pieces=re.findall(r'def part\d+ : List ℤ := \[([^]]*)\]',source)
    assert len(pieces)==2 and [int(x) for p in pieces for x in p.split(', ')]==sorted(integers)
    # Reconstruct Q by its POSITIVE expansion, never by forward quotient recurrence.
    for u in (16,17,24,32,40,64):
        powers=[power(mul(Q,Q),j) for j in range(u+1)];qu=[]
        for n in range(u):
            qu.append((sum(comb(u-1-j,n-j)*powers[j][0] for j in range(n+1)),
                       sum(comb(u-1-j,n-j)*powers[j][1] for j in range(n+1))))
        qu.append(powers[u])
        for s in range(2,u-1 if u>=32 else u-2):
            for k in range(1,s+1):
                K=sub(mul(qu[s],qu[k]),mul(qu[s+1],qu[k-1]))
                T=add(add(qu[k+1],mul(mul((2,0),Q),qu[k])),mul(mul(Q,Q),qu[k-1]))
                scale=(5,8) if u>=32 else (4,5)
                assert sign(sub(mul((scale[0],0),K),mul((scale[1],0),T)))>=0;ct['positive_expansion_unscaled_kernel_minors']+=1
    rng=Random(20261029853)
    for trial in range(90):
        r=6+trial%5;V=sorted(4+(trial*(j+1)*(j+3)+7*j)%17 for j in range(r));delta=3+trial%(V[0]-3);h=sum(t-1 for t in V);u=h-delta
        assert u>=16 and 13*(delta+1)<=3*(u+1)
        L=[1]
        for t in reversed(V):L=fastconv([1]*t,L)
        _,J=divided(L,u);b=J[delta-1:];d=[sub(z,b[n-1] if n else Z) for n,z in enumerate(b)];g=[z if sign(z)>0 else Z for z in d]
        assert all(sign(z)>0 for z in b)
        for n in range(1,len(b)-1):assert sign(determinant(b,n))>=0;ct['independent_natural_quotient_minors']+=1
        for n in range(2,len(g)-1):assert sign(determinant(g,n))>=0;ct['independent_natural_later_primitive_minors']+=1
        for alpha in {1,2,delta,u+1}:
            F=suffix_boxes(alpha,[2]*u+V);W=sum(V);tail=[max(0,F[n]-F[n-1]) for n in range(W,len(F))];M=tail.index(max(tail))
            for n in range(1,M):assert tail[n]**2>=tail[n-1]*tail[n+1];ct['independent_actual_padding_tail_minors']+=1
            ct['independent_many_factor_actual_hosts']+=1
        ct['independent_many_factor_profiles']+=1
    for R in (Fraction(1,3),Fraction(2,3),Fraction(1),Fraction(5,3),Fraction(2)):
        for _ in range(800):
            xm=rng.randint(1,300);x=rng.randint(0,int(R*xm));xp=rng.randint(0,x*x//xm)
            em=rng.randint(0,xm+1);emin=2*R*em;e=(emin.numerator+emin.denominator-1)//emin.denominator+rng.randint(0,20)
            epmin=2*R*e;ep=(epmin.numerator+epmin.denominator-1)//epmin.denominator+rng.randint(0,20)
            A=[max(0,a-b) for a,b in zip((xm,x,xp),(em,e,ep))]
            assert A[1]**2>=A[0]*A[2];ct['independent_rational_fast_source_triples']+=1
    if '--reconstruct-only' in sys.argv:
        print(json.dumps(dict(status='PASS_INDEPENDENT_MANY_FACTOR_CROSSING_RECONSTRUCTION',profiles=3,distinct_margins=449,counts=dict(ct),independent_state_sha256=sha.hexdigest())),flush=True);return
    kernels={'UnscaledHeadFastSource':kernel('UnscaledHeadFastSource',UNSCALED),
             'ManyFactorCICrossing':kernel('ManyFactorCICrossing',MANY),
             'ManyFactorCrossingCertificate':kernel('ManyFactorCrossingCertificate',['all_integer_margins'])}
    deps=['double_subdegree_CI_entrance_verification.json','mode_only_uniform_tail_closure_verification.json',
          'all_padding_CI_entrance_verification.json']
    for path in deps:
        v=json.loads((ROOT/path).read_text(encoding='utf8'))
        for n,digest in v['sha256'].items():assert hashlib.sha256((ROOT/n).read_bytes()).hexdigest()==digest,n
    files=['unscaled_head_and_fast_source_proof.tex','UnscaledHeadFastSource.lean','UnscaledHeadFastSource.log',
        'probe_unscaled_head_and_fast_source.py','probe_unscaled_head_and_fast_source.json',
        'many_factor_CI_crossing_proof.tex','ManyFactorCICrossing.lean','ManyFactorCICrossing.log',
        'ManyFactorCrossingCertificate.lean','ManyFactorCrossingCertificate.log','audit_many_factor_CI_crossing.py',
        'audit_many_factor_CI_crossing.json','emit_many_factor_crossing_certificate.py','verify_many_factor_CI_crossing.py',
        'double_subdegree_support_clarification.tex','DoubleSubdegreeCI.lean','DoubleSubdegreeCI.log',
        'finite_initial_ones_relative_derivative.tex','golden_signed_primitive_cut_closure.tex']+deps
    assert all((ROOT/f).exists() for f in files)
    out=dict(status='PASS_UNBOUNDED_ALL_MANY_FACTOR_CROSSINGS_AND_CONSTANT_FIVE_FACTOR_ENTRANCE_REDUCTION',new_scoped_reports=17,kernels=kernels,
        unscaled='PROVED ALLu>=32,K(s,k)>=8/5*T_kat2<=s<=u-2,1<=k<=s. ANYinterval-supportedLCN0=1,N1<=u/2,degree<=u-3hasUNSCALEDsameLCminorbudget. NEWu>=16INTERIORconstant5/4needsNODEGREEboundwhenN1<=u/3+1. ULCdegreeisu,notu-1.',
        fast_source='PROVEDANYnonnegativeLCtriple(xprev,x,xnext),x<=R*xprev,R>0,andANYnonnegativesourcewithBOTHgrowthratios>=2R:positivepart(x-source)tripleisLC. GeneralbinomialsourceE=(1+z)^uN,N>=0hasjE_j>=(u-j+1)Eprev. Thussourcecentrejwith13(j+1)<=3(u+1)payseveryprovedsubgoldenLCbackgroundtriple;backgroundpremisesretained.',
        many_factor='PROVED ALLu,ALLpaddingalpha>=1,EVERYdeletion-minimalCIdegreecrossingh>uwithr>=6:ACTUALpositiveDtailfromphysicalW=sumVhasLCatEVERYpre-first-tail-modecentre, equivalentlyALLpre-global-modeN>=W+1. δ1/2oldtheorems;δ>=3forcesALLdi>=δ,allcapacities>=4. Largestt<=u-11,unscaledheads+SIXnorms<1/4payENTIREnaturalquotientandlaterprimitive. Fullsourcecutwithdiscardedprefixandfast-sourcewindowclosesALLalphaexceptTHREEcompletefiniteprofiles,nowkernelchecked.',
        constant_factor_reduction='ENTIREunboundeduniversalactualLATE-D-LCentranceforallh>ureducestoMINIMALcrossingswithAT MOST FIVECI factors. Residual2<=r<=5,3<=di<=u,u+3<=h<=2u,h-min di<=u,NOcapacity3,andnosubsetdegreeu+1/u+2;fixeduandpaddingclampremainfinite. ANYseedpropagatesbyarbitraryCIinsertion. Noassertionthatthefive-factorentranceisalreadychecked.',
        exceptions='EXACTLY(u,V)=(15,4^6),(16,4^5,5),(20,5^6). ALL58paddinghosts/770minors/449distinctintegerkernelmarginsindependentlyrebuiltfrompositiveactualsuffixboxes. Notfiniteextrapolationatlargeru.',
        formal_scope='SEVENTEEN NEW scopedreportscountONCE:9UnscaledHeadFastSource,7ManyFactorCICrossing,1ManyFactorCrossingCertificate(propextonly). Actualquotient/ULC/CauchyBinet/window/signedcut/mode/insertionassemblyWRITTEN,notend-to-endLeancompositionformalization. WholefieldQAisexact;1600generalno-threeprofilesremainDIAGNOSTICONLY.',
        remaining='ALLat-most-five-factorcrossingsoutsideprovedseedsremain. ConvertingfurtherlateDLCtoALLown-cumulativeCstillneedsordinary/cumulativeentrancebudgets;earlierCremainsseparate. MasteractualLATE-Cthresholdu>=h-2unchanged. GeneralC/A2/originalunamplifiedUIremainOPEN;nooriginalnumericalboundupgrade.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',actual_late_C_threshold='u>=h-2 UNCHANGED',
        independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),state_sha256=qa['state_sha256'],QA=qa['counts'],
        unscaled_QA=uq['counts'],sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'many_factor_CI_crossing_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)

if __name__=='__main__':main()
