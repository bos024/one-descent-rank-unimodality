"""Independent integer minor certificates and closed-count/root-field reconstruction."""
from pathlib import Path
from collections import Counter
from fractions import Fraction as Q
import sys,json,time,hashlib,re,random
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_universal_renewal_rounding import closed_G
from verify_renewal_root_primitive_cut import ReciprocalRing

def power(f,a,m):
    v=f.one
    for _ in range(m):v=f.mul(v,a)
    return v
def append_prefix(F,v):
    return [1]+[sum(F[max(0,n-v):n]) for n in range(1,len(F))]
def reports():
    src=(ROOT/'ParameterizedRenewalResidual.lean').read_text();log=(ROOT/'ParameterizedRenewalResidual.log').read_text()
    assert not any(s in log for s in ['warning:','error:','sorryAx','ofReduceBool','failed']) and 'native_decide' not in src
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==9
    out={}
    for n,raw in rows:
        ax=[s.strip() for s in raw.split(',') if s.strip()];assert set(ax)<={'propext','Classical.choice','Quot.sound'};out[n]=ax
    return out
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=random.Random(811011)
    for t in list(range(3,42))+[90,200]:
        N=140 if t<=90 else 2*t+12
        h=[closed_G(t,n)-closed_G(t,n-1) for n in range(N+2)]
        top=Q(2)-Q(1,2**(t-1))
        theta=[Q(1),Q(7,5),Q(13,8),top-Q(1,2**(t+2)),top-Q(1,2**(2*t+2))]
        for θ in theta:
            if θ>=top:continue
            a,b=θ.numerator,θ.denominator
            pnum=(2*b-a)*2**(t-2);btail=2*pnum-b
            assert btail>0
            Cbnum=a*btail+max(btail*b,(a-b)**2)
            K=[b*h[n]-a*(h[n-1] if n else 0) for n in range(N+2)]
            for n in range(3,N+1):
                M=K[n]**2-K[n-1]*K[n+1]
                assert abs(M)*btail<=Cbnum*K[n-1],(t,θ,n)
                ct['independent_closed_counts_INTEGER_parameter_minor_checks']+=1
            ct['independent_complete_parameter_contexts']+=1
            sha.update(str((t,a,b,Cbnum,K[-3:])).encode())
    print(json.dumps(dict(phase='independent_integer_minors',counts=dict(ct))),flush=True)
    # Reconstruct U from the exact closed CDF rather than from its renewal recurrence.
    for t in range(2,12):
        f=ReciprocalRing(t);Nmax=72
        g=[closed_G(t,n) for n in range(Nmax+1)]
        h=[g[n]-(g[n-1] if n else 0) for n in range(Nmax+1)]
        U=[f.sub(f.sc(f.one,g[n]),f.sc(f.l,g[n-1] if n else 0)) for n in range(Nmax+1)]
        words=[[],[t]*7,[t+1],[t+4,t,t+2],sorted(rng.choices(range(t,t+9),k=5))]
        for V in words:
            F=h[:]
            for v in V:F=append_prefix(F,v)
            # Recover the numerator from P_t*F, without the positive numerator recurrence.
            P=[F[n]-sum(F[max(0,n-t):n]) for n in range(Nmax+1)]
            W=sum(V);assert P[0]==1 and P[1:t+1]==[0]*t and min(P)>=0 and all(v==0 for v in P[W+1:])
            G=[];v=0
            for x in F:v+=x;G.append(v)
            for r in [2,3,t+2,2*t+1]:
                rho=f.mul(power(f,f.l,r-2),power(f,f.sub(f.l,f.one),2))
                J=[f.one,f.sub(f.l,f.sc(f.one,2))]
                for k in range(2,r):J.append(f.mul(power(f,f.l,k-2),power(f,f.sub(f.l,f.one),2)))
                E=[]
                for n in range(Nmax+1):
                    v=f.zero
                    for i,j in enumerate(J):
                        if i<=n:v=f.add(v,f.mul(j,U[n-i]))
                    E.append(v)
                mass=f.mul(f.sub(f.l,f.one),power(f,f.l,r-2))
                for n in range(Nmax+1):
                    R=f.sub(f.sc(f.one,F[n]-(F[n-1] if n else 0)),f.sc(rho,G[n-r] if n>=r else 0))
                    expected=f.zero
                    for i in range(n+1):expected=f.add(expected,f.sc(E[n-i],P[i]))
                    assert R==expected
                    assert f.sign(f.sub(R,f.sc(f.one,P[n])))>=0
                    upper=f.add(f.sc(f.one,P[n]),f.sc(mass,sum(P[:max(0,n-1)])))
                    assert f.sign(f.sub(upper,R))>=0
                    ct['independent_ALLdelay_coupled_closed_count_and_Jkernel_reads']+=1
            # True finite-arm agreement and exact protected-head endpoint.
            if V:
                for alpha in [1,2,5]:
                    finite=[1 if n<=alpha else 0 for n in range(Nmax+1)]
                    for v in V:finite=append_prefix(finite,v)
                    assert finite[:len(V)+2]==F[:len(V)+2]
                    assert finite[len(V)+2]<F[len(V)+2]
                    ct['independent_finite_padding_protected_heads_with_FIRSTloss']+=1
            sha.update(str((t,V,P[:W+2],F[-3:])).encode())
        print(json.dumps(dict(order=t,phase='independent_coupled_source',reads=ct['independent_ALLdelay_coupled_closed_count_and_Jkernel_reads'])),flush=True)
    primary=json.loads((ROOT/'audit_parameterized_renewal_residual.json').read_text())
    assert primary['status']=='EXACT_QA_PASS_PARAMETERIZED_RESIDUAL_AND_ALL_DELAY_POSITIVE_COUPLED_SOURCE'
    local=['parameterized_renewal_residual_and_coupled_source_proof.tex','ParameterizedRenewalResidual.lean','ParameterizedRenewalResidual.log',
      'audit_parameterized_renewal_residual.py','audit_parameterized_renewal_residual.json','verify_parameterized_renewal_residual.py']
    deps=['universal_polynacci_minor_bounds_verification.json','universal_polynacci_minor_and_golden_residual_bounds_proof.tex',
      'ProbabilityQuadraticMinorEnvelope.lean','ProbabilityQuadraticMinorEnvelope.log','universal_renewal_rounding_verification.json',
      'universal_renewal_rounding_and_ordinary_C_bridge_proof.tex','UniversalRenewalRounding.lean','UniversalRenewalRounding.log',
      'verify_universal_renewal_rounding.py','verify_renewal_root_primitive_cut.py']
    out=dict(status='PASS_PARAMETERIZED_ALL_ORDER_RESIDUAL_ENVELOPES_AND_ALL_DELAY_POSITIVE_COUPLED_RENEWAL_SOURCE',new_scoped_reports=9,kernels=reports(),
      parameter_envelope='EVERYt>=3,1<=theta<2-2^(1-t):k=h_t-theta*z*h_t ALLpositivefromn2;ABS(M_k(n))<=C*kprev ALLn>=3,C=theta+max(1,(theta-1)^2/((2-theta)*2^(t-1)-1)). COMPLETEsymbolicbandandWHOLEprobabilityquadratictransport. NOfinite/spectralpremise.',
      adjacent_root='EVERYt>=3 theta=lambda_(t-1) ADMISSIBLE;2p=(2/theta)^(t-1)>1. Includesrootmatched3/4andALLadjacentorders.',
      sharp_uniform='EVERYtheta>=1 withtheta^2+2theta<=6:ALLt>=3 C=theta+1. UNIFORMconstantOPTIMALviaEXACTM_k(t1)/k_t=-(theta+1)+1/k_t,ast->infty. Goldenphi2recoveredasSPECIALcase,notrecounted.',
      coupled_identity='ANYnonnegativepolynomialN,F=N/P_t,G=F/(1-z),SIGNEDD=(1-z)F,ANYr>=2:rho=lambda^(r-2)(lambda-1)^2;EXACTD-rho*z^rG=N*(1+B_r/(1-A_t)),ALLBcoeffnonnegativeatindices>=2,mass(lambda-1)lambda^(r-2). Initialatomandrank1zeroRETAINED.',
      coupled_bound='ALLn:N_n<=D_n-rho*G_(n-r)<=N_n+(lambda-1)lambda^(r-2)SUM_i<=n-2N_i. rhoOPTIMALwhenN1,boundedresidual/exponentiallygrowingG,NOconjugateasymptotics. LowerboundNOTmonotonicity/C.',
      reference_and_actual_head='INFINITEorder-treferencefollowedANYcaps>=t,arbitraryorder,hasnonnegativeNviaNnew=1+z^(t+1)[v-t]+S_v(N-1);G_n>lambda*Gprev. Everyfiniteactual1alphaVwithhNONONEcaps>=t sharesEXACTreferenceheadthroughh+1,FIRSTlossath+2,soALLdelayboundsapplythroughh+1. NOgeneralfiniteactualextension.',
      formal_scope='NINEnewCLEANstandardaxiomSCOPEDreports:parameterboundaryidentities/ALLbandminorpayments/probabilitylowerbands/adjacentrootpowerentrance/uniformconstantarithmetic/ENTIREarbitrarynatural-delayCommRingidentity/wholefiniteforcingmass/positivefiniteconvolutionTWO-SIDEDbounds/numeratorrecursionalgebra. PreviousFIVEquadratictransportandTHREErenewalreportsREUSEDNOTrecounted. Fullseries/model/positivityandALLorderassemblyWRITTEN,notendtoendLeanactualcompositions. NOnewfiniteproofpremises.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',mixed_three_four_single_arm_C='OPEN',
      counts=dict(ct),primary_QA=primary['counts'],independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      local_files=local,dependency_files=deps,sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'parameterized_renewal_residual_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['sha256','kernels']}),flush=True)
if __name__=='__main__':main()
