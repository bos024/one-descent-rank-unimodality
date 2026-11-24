"""Independent diagonal/source/actual reconstruction of the analytic constant-three proof."""
from pathlib import Path
from math import comb
from random import Random
from fractions import Fraction
from collections import Counter
import hashlib,json,sys
from audit_arbitrary_Fibonacci_tail_late_C import add,sub,mul,sign
from verify_double_subdegree_CI_entrance import multiplicities
from verify_subdegree_CI_entrance import suffix_boxes
from verify_divided_CI_surplus_three_primitive import kernel
from probe_divided_CI_positive_primitive import divided
from audit_joint_structure import fastconv
ROOT=Path(__file__).resolve().parent
Z=(0,0)
NAMES=['background_right_ratio','source_density_convex','concave_positive_part_LC',
 'positive_scale_max','product_LC_triples','convex_tilt_source_positive_part_LC',
 'positive_lagrange_kernel_all_ranks','higher_source_uniform_cut_payment','interior_unit_budget',
 'unit_zero_row','small_count_norm','small_count_nonlong_geometry','all_nonlong_junction_scalar',
 'all_nonlong_junction_gap','small_count_perturbed_junction']

def intconv(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c

def fielddet(a,n):return sub(mul(a[n],a[n]),mul(a[n-1],a[n+1]))

def main():
    qa=json.loads((ROOT/'audit_convex_tilt_Lagrange_source.json').read_text(encoding='utf8'))
    assert qa['status']=='EXACT_QA_CONVEX_TILT_TERNARY_LAGRANGE_CONSTANT_THREE_UNDER_AUDIT'
    ct=Counter();sha=hashlib.sha256();N=48
    # Rebuild G from its rational denominator recurrence, not its closed coefficients.
    den=intconv(intconv([1,-2,1],[1,0,-2,0,1]),[1,-2]);num=[(1,0),(0,-2),(1,1)];G=[]
    for n in range(N+1):
        z=num[n] if n<len(num) else Z
        for j in range(1,min(n,len(den)-1)+1):z=sub(z,mul((den[j],0),G[n-j]))
        G.append(z);assert sign(z)>0
    assert G[1]==(4,-2) and G[2]==(14,-7)
    for e in range(9):
        Ge=[Z]*(N+e+1)
        for i,z in enumerate(G):
            for j in range(e+1):Ge[i+j]=add(Ge[i+j],mul((comb(e,j),0),z))
        for k in range(2,N+1):
            val=Z
            for l in range(1,k+1):
                top=l*comb(3*k,k-l);assert top%k==0
                val=add(val,mul((top//k,0),Ge[l]))
            j=k-1;u=3*j+e
            # A differential recurrence independently reconstructs the whole source.
            U=[1,u+4]
            for n in range(2,j+2):
                top=(u+4)*U[-1]+(n+2-u)*U[-2];assert top%n==0;U.append(top//n)
            direct=(U[j+1]+U[j-1],U[j-1]-2*U[j])
            assert val==direct and sign(sub(val,(26,-13)))>=0;ct['independent_Fuss_diagonal_identities']+=1
            sha.update(json.dumps([e,k,val],separators=(',',':')).encode())
    produced={(r['u'],tuple(r['V']),r['delta']) for r in qa['small_u14_u15_profiles']};keys=set();contexts=[]
    for u in (14,15):
        for r in range(4,u//3+2):
            for delta in range(3,u//(r-1)+1):
                for V in multiplicities(u+delta,u+delta):
                    if len(V)==r and min(V)-1>=delta:
                        key=(u,tuple(V),delta);assert key not in keys;keys.add(key);contexts.append((u,V,delta,True))
    assert keys==produced and len(keys)==27
    rng=Random(20261029897)
    for trial in range(85):
        r=4+trial%10;V=sorted(4+(trial*(j+2)*(j+5)+11*j)%23 for j in range(r));delta=3+trial%(V[0]-3);u=sum(t-1 for t in V)-delta
        if u>=14:contexts.append((u,V,delta,False))
    for u,V,delta,complete in contexts:
        L=[1]
        for t in reversed(V):L=fastconv([1]*t,L)
        E,J=divided(L,u);b=J[delta-1:];g=[]
        for n,z in enumerate(b):
            v=sub(z,b[n-1] if n else Z);g.append(v if sign(v)>0 else Z)
        assert all(sign(z)>0 for z in b)
        for n in range(1,len(b)-1):assert sign(fielddet(b,n))>=0;ct['independent_natural_quotient_LC_minors']+=1
        for n in range(2,len(g)-1):assert sign(fielddet(g,n))>=0;ct['independent_natural_later_primitive_minors']+=1
        for j in range(2,delta+1):
            assert sign((E[j+1]+E[j-1],E[j-1]-2*E[j]))>0;ct['independent_true_source_curvatures']+=1
        alphas=range(1,(2*u+delta)//2+2) if complete else {1,2,delta,u+delta+2}
        for alpha in alphas:
            F=suffix_boxes(alpha,[2]*u+V);W=sum(V);g=[max(0,F[n]-F[n-1]) for n in range(W,len(F))];M=g.index(max(g))
            for n in range(1,M):assert g[n]**2>=g[n-1]*g[n+1];ct['independent_actual_tail_LC_minors']+=1
            ct['independent_actual_hosts']+=1
            ct['independent_small_complete_hosts']+=complete
        ct['independent_CI_profiles']+=1
    # Direct positive-suffix-box reconstruction of the stronger relative-LC failure.
    V=[5,29,51];u=79;W=sum(V);A=suffix_boxes(1,[2]*u+V);B=suffix_boxes(250,[2]*u+V)
    da=[max(0,A[n]-A[n-1]) for n in range(W,len(A))];db=[B[n]-B[n-1] for n in range(W,len(B))];n=44
    rel=da[n]**2*db[n-1]*db[n+1]-da[n-1]*da[n+1]*db[n]**2
    control=qa['actual_relative_LC_negative_control']
    assert da.index(max(da))==control['first_tail_mode']==51 and rel==control['margin']<0
    assert da[n]**2>=da[n-1]*da[n+1]
    for _ in range(9000):
        X=rng.randint(1,10000);x=rng.randint(0,X);Zp=rng.randint(0,x*x//X)
        em=rng.randint(0,2*X);e=em+rng.randint(0,1000);ep=2*e-em+rng.randint(0,1000)
        A=[max(0,a-b) for a,b in zip((X,x,Zp),(em,e,ep))]
        assert A[1]**2>=A[0]*A[2];ct['independent_unit_tilt_clipped_LC_triples']+=1
    if '--reconstruct-only' in sys.argv:
        print(json.dumps(dict(status='PASS_INDEPENDENT_CONVEX_TILT_TERNARY_DIAGONAL_RECONSTRUCTION',counts=dict(ct),small_profiles=27,relative_control=rel,independent_state_sha256=sha.hexdigest())),flush=True);return
    kernels={'ConvexTiltLagrangeSource':kernel('ConvexTiltLagrangeSource',NAMES)}
    deps=['many_factor_CI_crossing_verification.json','double_subdegree_CI_entrance_verification.json',
          'mode_only_uniform_tail_closure_verification.json']
    for path in deps:
        d=json.loads((ROOT/path).read_text(encoding='utf8'))
        for name,digest in d['sha256'].items():assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
    files=['convex_tilt_Lagrange_three_factor_proof.tex','ConvexTiltLagrangeSource.lean','ConvexTiltLagrangeSource.log',
        'audit_convex_tilt_Lagrange_source.py','audit_convex_tilt_Lagrange_source.json','verify_convex_tilt_Lagrange_three_factor.py',
        'many_factor_CI_crossing_proof.tex','unscaled_head_and_fast_source_proof.tex',
        'finite_initial_ones_relative_derivative.tex','golden_signed_primitive_cut_closure.tex']+deps
    out=dict(status='PASS_UNBOUNDED_CONVEX_TILT_TERNARY_SOURCE_AND_CONSTANT_THREE_FACTOR_ENTRANCE',new_scoped_reports=15,kernels=kernels,
        convex_source='PROVEDANYnonnegativeLCbackground,xmid<=R*xprev,R>0,ANYnonnegativesource:sourcecur>=R*sourceprevANDsourceNext-2R*sourceCur+R2*sourcePrev>=0implypositivepart(background-source)LC. Exactsource-densityconvexidentityandFULLpositiveclippingkernelproved. BackgroundLC/ratiohypothesesretained.',
        ternary_diagonal='PROVEDALLj>=1,u>=3j:Q4(u,j)=U4(j+1)-2phiU4(j)+phi2U4(j-1)>=26-13phi>4,U_r=[zj](1+z)^u/(1-z)^r. GesselTheorem2.1.1eq2.1.4withw=t(1+w)^3givesEXACTG(w)(1+w)^e;ALLGcoefficientspositivebyunboundedbinary-exponentialkernelproof. Higher r>=4 givesQ_r>r atALLj>=2,u>=3j,soEVERYtruefirstcapacityunitcutispaid.',
        four_or_more='PROVEDALLdeletion-minimalCIcrossingsr>=4,ALLu,ALLcapacities/padding:actualpositiveDtailfromW=sumVhasLCatEVERYpre-first-tail-modecentre,ALLpre-global-modeN>=W+1. ONEunboundedanalyticproofatALLu>=14usesunitinteriorheadalreadyu12,norm<3/5,concavegapfor3<=oldCount<=u/3,andternary-sourceconvexstartup. ALLu<=13usesOLDregisteredtheorem. NO NEW FINITE HOST ENTRANCE OR EXCEPTION CERTIFICATE.',
        constant_three_reduction='ENTIREuniversalactualLATE-D-LCentranceforh>unowreducestoONLYTWOorTHREECIfactorminimalcrossings. Remainingu>=14,r2/3,3<=di<=u,u+3<=h<=2u,h-min di<=u,andmayhavenosubsetdegreeu+1/u+2. ArbitraryotherCIfactorspropagatebyregisteredexactinsertion. Remainingtwo/threefactorentranceNOTsolved.',
        formal_scope='FIFTEENNEWscopedstandardaxiomkernelreports:FULLconvex-sourcepositiveclipping,densityidentity,all-rankpositivityofdiagonalkernel,uniformr-cutpayment,u12unithead,generic3..u/3junctionandgeometry. FormalLagrangeinversionisastandardPRIMARY-literatureinput;power-series/rationalkernel/composition/coefficient/sourceandactualwordassemblyWRITTEN,notend-to-endLeanformalpowerseriesorcomposition. ALL27smallu14/15contextsareQAONLY,noproofcutoff.',
        primary_source=qa['primary_source'],actual_relative_LC_control=control,
        remaining='ONLY2/3-factorlateDLCentrancesremainafterprovedseeds. FurtherlateDLCmuststillbejoinedtoactualordinary/cumulativeCentrancebudgets;earlyC,A2andoriginalUIremainOPEN. ActualLATE-Cthresholdu>=h-2UNCHANGED;nooriginalnumericalboundupgrade.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',actual_late_C_threshold='u>=h-2 UNCHANGED',
        new_finite_entrance_certificates=0,independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),
        state_sha256=qa['state_sha256'],QA=qa['counts'],sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'convex_tilt_Lagrange_three_factor_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)

if __name__=='__main__':main()
