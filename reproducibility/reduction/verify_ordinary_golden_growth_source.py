"""Independently reconstruct from positive suffix boxes and complete interval products."""
from pathlib import Path
import sys,json,re,hashlib
from collections import Counter
from random import Random
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
from audit_arbitrary_Fibonacci_tail_late_C import sign,add,sub,mul,power
Q=(-1,1);PSI=(1,-1);ONE=(1,0);ZERO=(0,0)
NAMES=['kernel_box','signed_power_box','interval_spectral_factor','finite_product_strict','weighted_kernel_lower',
       'convolution_current_atom','positive_kernel_covers_mass','golden_spectral_payment','cumulative_density_step',
       'ordinary_density_golden_transfer','actual_source_resource','actual_source_increment_resource']

def conv(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c

def window(a,t):
    out=[0]*(len(a)+t-1);s=0
    for n in range(len(out)):
        if n<len(a):s+=a[n]
        if 0<=n-t<len(a):s-=a[n-t]
        out[n]=s
    return out

def infinite_ones(U,N):
    a=[0]
    for t in U:
        a=[0]+window(a,t)
        for j in range(t-1):a[j]+=1
    F=[1,1]
    for n in range(2,N+1):F.append(F[-1]+(a[n-2] if n-2<len(a) else 0))
    return F

def kernels():
    src=(ROOT/'OrdinaryGoldenGrowthSource.lean').read_text();log=(ROOT/'OrdinaryGoldenGrowthSource.log').read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(x in log for x in ('error:','warning:','sorryAx','ofReduceBool','failed'))
    assert log.count('depends on axioms:')==len(NAMES)
    out={}
    for n in NAMES:
        m=re.search(r"'OrdinaryGoldenGrowthSource\."+n+r"' depends on axioms: \[([^]]*)\]",log);assert m,n
        ax={a.strip() for a in m.group(1).split(',') if a.strip()};assert ax<={'propext','Classical.choice','Quot.sound'};out[n]=sorted(ax)
    return out

def main():
    qa=json.loads((ROOT/'audit_ordinary_golden_growth_source.json').read_text())
    assert qa['status']=='EXACT_QA_UNIVERSAL_ORDINARY_GOLDEN_GROWTH_UNDER_AUDIT'
    rng=Random(20261031166);ct=Counter();sha=hashlib.sha256();profiles=[]
    for t in range(3,19):
        for r in range(1,6):
            V=[t]*r;h=r*(t-1)
            for u in {0,max(0,h-2),h-1,h,h+1,2*h}:profiles.append((u,V))
    for _ in range(50):
        V=sorted(rng.choices(range(3,18),k=rng.randint(1,7)));h=sum(t-1 for t in V);profiles.append((rng.randint(0,2*h),V))
    for u,V in profiles:
        W=sum(V);h=W-len(V);w=u+len(V);d=u+h;T=max(W,w+2);Nmax=max(T+4,w+2+d+2)
        E=[1]
        for t in [2]*u+V:E=conv(E,[1]*t)
        I=infinite_ones([2]*u+V,Nmax);rho=ONE
        for t in V:rho=mul(rho,mul(Q,sub(ONE,power(PSI,t))))
        assert sign(rho)>0 and sign(sub(ONE,rho))>0
        K=[ONE]
        for s in range(1,Nmax-w-1):K.append(sub(ONE,mul(Q,K[-1])))
        for N in range(T,Nmax+1):
            s=N-w-2;U=ZERO
            for i in range(min(s,d)+1):U=add(U,mul((E[i],0),K[s-i]))
            assert sign(sub(U,ONE))>=0
            assert (-I[N],I[N-1])==sub(U,mul(rho,power(PSI,N-W)))
            assert sign((-I[N],I[N-1]))>0;ct['independent_exact_positive_kernel_golden_gap_reads']+=1
        for alpha in {1,2,max(1,h-u+1)}:
            F=suffix_boxes(alpha,[2]*u+V)[:alpha+2*u+W+1]+[0]
            M=F.index(max(F));I2=infinite_ones([2]*u+V,len(F)-1)
            for n in range(1,M+1):
                assert F[n]*I2[n-1]<=F[n-1]*I2[n];ct['independent_finite_cumulative_density_reads']+=1
            for N in range(T,len(F)):
                if F[N-1]:assert sign((-F[N],F[N-1]))>0
                else:assert F[N]==0
                ct['independent_all_padding_ordinary_golden_reads']+=1
                if h>u and N>=W+1 and F[N]>=F[N-1]>=F[N-2] and F[N-1]>F[N-2]:
                    x=F[N-1]-F[N-2];y=F[N]-F[N-1]
                    assert sign(sub((2*x-y,0),mul(power(Q,2),(x,0))))>0;ct['independent_guarded_source_increment_reads']+=1
            ct['independent_actual_hosts']+=1
        sha.update(json.dumps([u,V,T,rho,I[T-1:T+2]],separators=(',',':')).encode());ct['independent_CI_profiles']+=1
    deps=['golden_tail_large_shift_C_verification.json']
    for name in deps:
        dep=json.loads((SOURCE/name).read_text())
        for f,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/f).read_bytes()).hexdigest()==digest,f
    files=['ordinary_golden_growth_source_proof.tex','OrdinaryGoldenGrowthSource.lean','OrdinaryGoldenGrowthSource.log',
           'audit_ordinary_golden_growth_source.py','audit_ordinary_golden_growth_source.json','verify_ordinary_golden_growth_source.py',
           'finite_initial_ones_relative_derivative.tex','ordinary_relative_growth.tex']+deps
    def fp(f):return ROOT/f if (ROOT/f).exists() else SOURCE/f
    out=dict(status='PASS_UNIVERSAL_ORDINARY_GOLDEN_GROWTH_AND_LATE_SOURCE_RESOURCE',new_scoped_reports=12,kernels={'OrdinaryGoldenGrowthSource':kernels()},
        state_sha256=qa['state_sha256'],QA=qa['counts'],independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),new_finite_entrance_certificates=0,
        ordinary_ceiling='PROVED ALLu/h,ALLactual1alpha2uV nonemptyV>=3,ALLcapacities/counts/paddings: F_N<phiFprev forEVERYN>=max(W,u+r+2) whenFprev>0,zerootherwise. ENTIREtail incl aftermode and terminal support. No count wedge, no derivative-LC input needed for this theorem. Ifh>=u+2 startW;ifh=u+1 startW+1; one earlier edge can fail on actual arms.',
        exact_identity='PROVED infiniteINITIAL-one padding FIXEDbinaryu: phiFprev-F_N=U_(N-u-r-2)-rho*(-q)^(N-W),U=E/((1-z)(1+qz)),rho=prod q(1-(-q)^t) in(0,1). ALL coefficient reads past bothW andfirst finite-count loss, including beyond ENTIRECI support. Positive-kernel ALLprefix mass>=1 pays the complete conjugate atom.',
        finite_padding_density='PROVED actual Ffinite/FinfiniteINITIAL is nonincreasing through FIRST ordinary mode, by adding shared atom and cumulatively transporting the registered decreasing positive-D density. Aftermode ordinary UI supplies immediate ceiling. RelativeLC of this density is NOT asserted.',
        source_resources='PROVED source E_N=2Fprev-F_N>=q^2Fprev on the universal ordinary tail,strictifFprev>0. Forh>u,N>=W+1 and NONNEGATIVE actual ordinary slopes atN-1,N,registered goldenD additionally gives DeltaE_N=2Dprev-D_N>=q^2Dprev,strictifDprev>0. The clipped-D identity is NOT used outside that signed-slope guard. These source bounds do NOT alone prove every source-convolution/S comparison.',
        formal_scope='TWELVE NEW scoped standard-axiom reports include ALL-natural kernel/spectral inductions,strict finite-product induction,unbounded finite weighted-sum and cumulative-density transport. Exact model/conjugate/physical mode assembly written,not end-to-end actual-arm Lean. Earlier goldenD reports reused ONLY for source-INCREMENT corollary,not recounted. Every finite profile QA ONLY,NO finite premise.',
        remaining='General ordinary adjacent LC at boundary,shorter-shift lateC outside whole-arm cones,earlierC,complete A2 and original unamplified coefficient UI remain OPEN. Universal ordinary growth does not equate cumulativeLC with coefficientUI and does not upgrade original count6 frontier.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',sha256={f:hashlib.sha256(fp(f).read_bytes()).hexdigest() for f in files})
    (ROOT/'ordinary_golden_growth_source_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('sha256','kernels')}),flush=True)

if __name__=='__main__':main()
