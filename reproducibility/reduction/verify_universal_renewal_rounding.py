"""Independent reciprocal-root ring, closed binomial counts and positive suffix-box bridge QA."""
from pathlib import Path
from collections import Counter
from itertools import accumulate
from math import comb
from random import Random
import sys,json,time,hashlib,re
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_renewal_root_primitive_cut import ReciprocalRing
from verify_subdegree_CI_entrance import suffix_boxes
def closed_G(t,n):
    if n<0:return 0
    return sum((-1)**j*comb(n-t*j,j)*2**(n-(t+1)*j) for j in range(n//(t+1)+1))
def reports():
    src=(ROOT/'UniversalRenewalRounding.lean').read_text(encoding='utf8');log=(ROOT/'UniversalRenewalRounding.log').read_text(encoding='utf8')
    assert not any(x in log for x in ['warning:','error:','sorryAx','ofReduceBool','failed']) and 'native_decide' not in src
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==3
    out={}
    for n,raw in rows:
        ax=[x.strip() for x in raw.split(',') if x.strip()];assert set(ax)<={'propext','Classical.choice','Quot.sound'};out[n]=ax
    return out
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();data=json.loads((ROOT/'universal_renewal_rounding_root_data.json').read_text())
    assert [r['t'] for r in data]==list(range(2,17))+[20,25,32]
    for row in data:
        t,N=row['t'],row['N'];f=ReciprocalRing(t);powers=[f.one]
        for _ in range(t):powers.append(f.mul(powers[-1],f.q))
        def convert(v):
            out=f.zero
            for a,p in zip(v,powers):out=f.add(out,f.sc(p,a))
            return out
        g=[closed_G(t,n) for n in range(N+1)];h=[g[n]-(g[n-1] if n else 0) for n in range(N+1)]
        assert row['g']==g and row['h']==h
        for n in range(N+1):
            U=f.sub(f.sc(f.one,g[n]),f.sc(f.l,g[n-1] if n else 0))
            assert convert(row['U'][n])==U and f.sign(U)>0
            c=f.sub(f.sc(f.one,h[n]),f.sc(f.l,h[n-1] if n else 0))
            if n:
                assert f.sign(f.sub(f.one,U))>0 and f.sign(f.add(f.one,c))>0 and f.sign(f.sub(f.one,c))>0
                ct['independent_closed_binomial_all_order_strict_bounds']+=1
            sha.update(str((t,n,U,c)).encode())
        B=[f.one]
        for i in range(1,t):B.append(f.sub(f.mul(f.l,B[-1]),f.one))
        assert f.mul(f.l,B[-1])==f.one
        for i in range(t):
            ai=f.sub(B[i],B[i+1] if i+1<t else f.zero)
            assert ai==powers[t-i] and f.sign(ai)>0
            ct['independent_WHOLE_polynomial_root_normalizer_coefficients']+=1
    rng=Random(2026110191)
    cases=[(rng.randint(1,80),[2]*rng.randint(0,35)+sorted(rng.randint(3,15) for _ in range(rng.randint(1,14)))) for _ in range(420)]
    cases +=[(a,[2]*u+[t]*r) for t in range(3,9) for a in [1,2,15] for u in [0,1,10,40] for r in [1,7,12]]
    for alpha,U in cases:
        t=max(U);F=suffix_boxes(alpha,U);h=[closed_G(t,n)-closed_G(t,n-1) for n in range(len(F))]
        a=next(n for n in range(len(F)) if F[n]!=h[n]);assert a>=3 and F[a]<h[a]
        D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];L=D.index(max(D))
        if not all(F[n]**2>=F[n-1]*F[n+1] for n in range(a,L)):continue
        G=list(accumulate(F))
        for N in range(4,L+1):
            for k in range(1,N-2):
                assert G[k]*D[N-1]>=G[k-1]*D[N];ct['independent_ALL_explicit_shift_C_payments']+=1
        ct['independent_actual_TRUE_firstdefect_ordinary_premise_hosts']+=1
    qa=json.loads((ROOT/'audit_universal_renewal_rounding.json').read_text());assert qa['status']=='EXACT_QA_PASS_UNIVERSAL_RENEWAL_ROUNDING_AND_CONDITIONAL_ORDINARY_C_BRIDGE'
    local=['universal_renewal_rounding_and_ordinary_C_bridge_proof.tex','UniversalRenewalRounding.lean','UniversalRenewalRounding.log',
      'audit_universal_renewal_rounding.py','audit_universal_renewal_rounding.json','universal_renewal_rounding_root_data.json','verify_universal_renewal_rounding.py']
    deps=['first_missing_renewal_envelope.tex','ordinary_tail_to_complete_C_proof.tex','ordinary_tail_to_complete_C_verification.json',
      'OrdinaryTailToCompleteC.lean','OrdinaryTailToCompleteC.log','prefix_tp2.tex','formal_arm_extensions.tex',
      'audit_renewal_root_primitive_cut.py','verify_renewal_root_primitive_cut.py','verify_subdegree_CI_entrance.py']
    out=dict(status='PASS_ALL_ORDER_STRICT_RENEWAL_ROUNDING_AND_UNIVERSAL_CONDITIONAL_ORDINARY_C_BRIDGE',new_scoped_reports=3,kernels=reports(),
      all_order_rounding='UNCONDITIONAL ALLt>=2/n>=1: -1<h_t(n)-lambda_t*h_t(n-1)<1. qsumq^i=1,lambda1/q. Noexceptionalband,NOrootconjugates/spectralnorm/irreducibilitypremise.',
      exact_probability_identity='WHOLEP_t=(1-lambda*z)B_t and(1-z)B_t=1-A_t, a_i=q^(t-i+1)>0,sum1. U=(1-A)^-1;U0=1,ALLn>=1 0<Un<1 byfinitepositiveprobabilityrenewal. EXACT(1-lambda*z)G_t=U and(1-lambda*z)H_t=(1-z)U. PositivecumulativegapALLn>=0 isUn<=1.',
      universal_actual_bridge='CONDITIONALANYactualnormalizedincreasingnonrectarm,maxpartt>=2,FIRSTdifferenceafromH_t,FIRSTDmodeL: ordinaryFLCatEVERYcentre a<=n<L=>FULLC EVERYcurrent/EVERYshift. Firstintegerloss+NEWstrictallorderrounding=>F_a<lambdaFprev,protectedGgapspositive;OLDfullboundedordinary-to-GbridgepaysALLlaterreads,afterLautomatic. NoDLC/strongminor/actualCDFLCpremise.',
      formal_scope='THREENEWcleanstandard-axiomSCOPEDgenericreports:ENTIREunboundedfiniteprobabilityrenewal0<U<=1andstrictn>=1;ENTIREstrictsignedincrementbound;WHOLEarbitraryCommRingpolynomialmixturenormalizeridentity. OLDfirstloss/boundedordinary-CkernelREUSED/NOTrecounted. RootBidentification/formalseries/actualfirstdefectassemblyWRITTEN,NOTendtoendLeanactualcompositions. NewfiniteexacttestsQAONLY.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',ordinary_LC_premise='NOTASSERTEDforarbitraryarms;actualcounter1alpha2^20 3^6 atcentre19 negative-4^6 yetFULLCknown.',
      counts=dict(ct),primary_QA=qa['counts'],independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      local_files=local,dependency_files=deps,sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'universal_renewal_rounding_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['sha256','kernels']}),flush=True)
if __name__=='__main__':main()
