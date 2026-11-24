"""Independent closed binomial counts and reciprocal-root probability/perspective identities."""
from pathlib import Path
from collections import Counter
import sys,json,time,hashlib,re
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_universal_renewal_rounding import closed_G
from verify_renewal_root_primitive_cut import ReciprocalRing
from verify_ternary_forward_inverse import qa,qm,qs,sub
def reports():
    src=(ROOT/'ProbabilityQuadraticMinorEnvelope.lean').read_text(encoding='utf8');log=(ROOT/'ProbabilityQuadraticMinorEnvelope.log').read_text(encoding='utf8')
    assert not any(x in log for x in ['warning:','error:','sorryAx','ofReduceBool','failed']) and 'native_decide' not in src
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==5
    out={}
    for n,raw in rows:
        ax=[x.strip() for x in raw.split(',') if x.strip()];assert set(ax)<={'propext','Classical.choice','Quot.sound'};out[n]=ax
    return out
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();cp=(2,1)
    for t in list(range(2,71))+[100,300,1000]:
        N=210 if t<=70 else 3*t+8
        h=[closed_G(t,n)-closed_G(t,n-1) for n in range(N+2)]
        K=[(h[n]-(h[n-1] if n else 0),-(h[n-1] if n else 0)) for n in range(len(h))]
        for n in range(1,N+1):
            M=h[n]**2-h[n-1]*h[n+1];assert -h[n-1]<=M<=h[n-1]
            ct['independent_closed_binomial_ALLorder_ordinary_minor_reads']+=1
            if t>=3 and n>=3:
                assert qs(K[n-1])>0
                M=sub(qm(K[n],K[n]),qm(K[n-1],K[n+1]));b=qm(cp,K[n-1])
                assert qs(qa(b,M))>=0 and qs(sub(b,M))>=0
                ct['independent_ALLorder_SHARP_golden_residual_minor_reads']+=1
        if t<len(h)-1:
            assert h[t]**2-h[t-1]*h[t+1]==h[t-1]
            if t>=3:
                M=sub(qm(K[t+1],K[t+1]),qm(K[t],K[t+2]))
                assert M==sub((1,0),qm(cp,K[t]))
                assert K[t]==(2**(t-2),-2**(t-2));ct['independent_exact_SHARPNESS_orders']+=1
        sha.update(str((t,h[-4:],K[t] if t<=N else None)).encode())
    # Verify every recurrence/source/denominator input of the written ALL-order assembly.
    for t in range(2,13):
        f=ReciprocalRing(t);N=100;h=[closed_G(t,n)-closed_G(t,n-1) for n in range(N+3)]
        powers=[f.one]
        for _ in range(t):powers.append(f.mul(powers[-1],f.q))
        weights=[powers[t-i] for i in range(t)];mass=f.zero
        for a in weights:
            assert f.sign(a)>0 and f.sign(f.sub(f.one,a))>0;mass=f.add(mass,a)
        assert mass==f.one
        d=f.sub(f.sc(f.one,2),f.l);assert d==powers[t]
        e=[f.sub(f.sc(f.one,h[n]),f.sc(f.l,h[n-1] if n else 0)) for n in range(N+2)]
        w=[f.sub(f.mul(f.l,e[n]),e[n+1]) for n in range(N+1)]
        for n in range(2,t+2):
            if n<t:formula=f.sub(f.zero,f.mul(d,e[n]))
            elif n==t:formula=f.sub(f.one,f.mul(d,e[n]))
            else:formula=f.add(f.sc(f.one,-1),f.mul(d,f.sub(f.one,e[n])))
            assert w[n]==formula and f.sign(f.add(w[n],f.one))>0
            ct['independent_COMPLETE_symbolic_probability_lower_band_reads']+=1
        for n in range(t+2,N+1):
            ee=ww=HH=f.zero
            for i,a in enumerate(weights):
                j=n-i-1;ee=f.add(ee,f.mul(a,e[j]));ww=f.add(ww,f.mul(a,w[j]));HH=f.add(HH,f.sc(a,h[j-1]))
            assert ee==e[n] and ww==w[n]
            assert f.sign(f.sub(f.sc(f.one,h[n-1]),HH))>=0
            M=h[n]**2-h[n-1]*h[n+1]
            assert f.add(f.mul(e[n],e[n]),f.sc(w[n],h[n-1]))==f.sc(f.one,M)
            ct['independent_full_probability_rec_and_SUPERdenominator_and_MINOR_identities']+=1
    primary=json.loads((ROOT/'audit_universal_polynacci_minor_bounds.json').read_text())
    assert primary['status']=='EXACT_QA_PASS_UNIVERSAL_SHARP_POLYNACCI_AND_GOLDEN_RESIDUAL_MINOR_ENVELOPES'
    local=['universal_polynacci_minor_and_golden_residual_bounds_proof.tex','ProbabilityQuadraticMinorEnvelope.lean',
      'ProbabilityQuadraticMinorEnvelope.log','audit_universal_polynacci_minor_bounds.py','audit_universal_polynacci_minor_bounds.json',
      'verify_universal_polynacci_minor_bounds.py']
    deps=['universal_renewal_rounding_verification.json','universal_renewal_rounding_and_ordinary_C_bridge_proof.tex',
      'UniversalRenewalRounding.lean','UniversalRenewalRounding.log','verify_universal_renewal_rounding.py',
      'verify_renewal_root_primitive_cut.py','verify_ternary_forward_inverse.py']
    out=dict(status='PASS_ALL_ORDER_SHARP_ORDINARY_AND_GOLDEN_RESIDUAL_MINOR_ENVELOPES_BY_PROBABILITY_QUADRATIC_TRANSPORT',new_scoped_reports=5,kernels=reports(),
      ordinary='UNCONDITIONAL EVERYt>=2/n>=1:ABS(h_n2-hprev*hnext)<=hprev. CONSTANT1SHARP,attainedatn=tandn1. NOexceptionalorder/band/spectral/irreducibilitypremise.',
      golden_residual='UNCONDITIONAL EVERYt>=3/n>=3:K=h_t-phi*z*h_t hasALLK_n>0forn>=2 andABS(M_K(n))<=phi2*Kprev. CONSTANTphi2SHARPuniformlyt:EXACTM_K(t1)=1-phi2*K_t,K_t=(2-phi)*2^(t-2). Ratio->-phi2ast->infty.',
      mechanism='NEWprobabilityquadraticperspective:positiveprobweights,e/wEXACTrenewals,HpositiveSUPERSOLUTION=>w>=-C ande2+H*w<=C*H propagatefromCOMPLETEorder-tband. UpperinequalityequivNONNEGATIVEquadraticALLrealx,weightedCauchytransportplusHgap. Exactminor=e2+H*w. EntireNatinductionkernelchecked.',
      symbolic_entrance='NOnewFINITEpremise. ALLt hband2..t1:0/P/1-2Pminors,w=-d*e/1-d*e/-1+d(1-e);UNIVERSALroundingpays. Goldenband3..t2:0/positive/1-phi2*K_t/(phi*K_t1+q2);lowerWpaidbyd*K_t<1,completeboundaryformulas. qphi<=2/3;K_t1>=3-4qphi>=qphi2. AllwrittenbandscoverEVERYtincludingemptygeometricrangeatt3.',
      formal_scope='FIVENEWcleanstandardaxiomSCOPEDreports:quadraticperspectiveequivalence,arbitraryfiniteweightedprobabilitytransport,ENTIREnatural-indexprobabilityquadraticinvariant,exactminorinterpretation/fullboundimplication,andCOMPLETEsymbolicgeometric/firsttwo-boundaryminoridentities. Actualpolynacci/goldenidentificationandALLtbandassemblyWRITTEN,NOTendtoendLeancompositions. NOnewfiniteproofpremise;alltestsQAonly.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',mixed_three_four_single_arm_C='OPEN',
      counts=dict(ct),primary_QA=primary['counts'],independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      local_files=local,dependency_files=deps,sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'universal_polynacci_minor_bounds_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['sha256','kernels']}),flush=True)
if __name__=='__main__':main()
