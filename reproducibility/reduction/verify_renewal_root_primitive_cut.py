"""Independent reciprocal-root ring and top-down bilateral kernel reconstruction."""
from pathlib import Path
from math import comb
from collections import Counter
import re,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent

class ReciprocalRing:
    def __init__(self,t):
        self.t=t;self.zero=(0,)*t;self.one=(1,)+(0,)*(t-1)
        self.l=(0,1)+(0,)*(t-2);self.q=(-1,)*(t-1)+(1,);self.cache={}
        assert self.mul(self.l,self.q)==self.one
    def add(self,a,b):return tuple(x+y for x,y in zip(a,b))
    def sub(self,a,b):return tuple(x-y for x,y in zip(a,b))
    def sc(self,a,c):return tuple(c*x for x in a)
    def mul(self,a,b):
        p=[0]*(2*self.t-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):p[i+j]+=x*y
        for k in range(len(p)-1,self.t-1,-1):
            for j in range(self.t):p[k-self.t+j]+=p[k]
        return tuple(p[:self.t])
    def rootpoly(self,n,M):
        v=1;s=1
        for _ in range(self.t):s*=M;v=v*n-s
        return v
    def interval(self,bits):
        if bits not in self.cache:
            M=1<<bits;lo=M;hi=2*M
            while hi-lo>1:
                mid=(lo+hi)//2
                if self.rootpoly(mid,M)<0:lo=mid
                else:hi=mid
            self.cache[bits]=(lo,hi,M)
        return self.cache[bits]
    def sign(self,a):
        if a==self.zero:return 0
        bits=max(128,4*max(abs(v).bit_length() for v in a)+128)
        while bits<=16384:
            lo,hi,M=self.interval(bits);A=B=a[-1];s=1
            for c in reversed(a[:-1]):
                s*=M;v=[A*lo,A*hi,B*lo,B*hi];A=min(v)+c*s;B=max(v)+c*s
            if A>0:return 1
            if B<0:return -1
            bits*=2
        raise ArithmeticError('Nonzero sign unresolved; no numerical zero inferred.')

def reports(name,count):
    src=(ROOT/(name+'.lean')).read_text(encoding='utf8');log=(ROOT/(name+'.log')).read_text(encoding='utf8')
    assert not any(x in log for x in ['warning:','error:','sorryAx','ofReduceBool','failed'])
    assert 'native_decide' not in src
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==count
    out={}
    for name,raw in rows:
        a=[x.strip() for x in raw.split(',') if x.strip()];assert set(a)<={'propext','Classical.choice','Quot.sound'};out[name]=a
    return out

def main():
    started=time.monotonic();ct=Counter();sha=hashlib.sha256()
    models=[[comb(30,n) for n in range(31)]]
    J=[5]
    for n in range(13):J.append(J[-1]+comb(12,n))
    models.append(J+[J[-1],J[-1]//2,J[-1]//3,J[-1]//7])
    for t in range(2,15):
        f=ReciprocalRing(t);p=t-1
        B=[f.one]
        for i in range(1,t):B.append(f.sub(f.mul(f.l,B[-1]),f.one))
        assert f.mul(f.l,B[-1])==f.one
        for ell in list(range(9))+[15,23]:
            U=ell+t-2;h=ell+2;N=U+7
            g=[0]*(p+h)
            for i in range(p):
                for j in range(h):g[i+j]+=1
            g[p]+=1
            L=[];v=f.zero
            for n in range(N+1):
                v=f.add(f.mul(f.q,v),f.sc(f.q,g[n] if n<len(g) else 0));L.append(v)
            # Reconstruct K from its finite upper endpoint, without a geometric cumulative formula.
            K={U+1:f.zero}
            for j in range(U+1,-7,-1):
                wx=f.zero
                for s in range(p):
                    if j-s<=-1:
                        z=f.one
                        for _ in range(s-j):z=f.mul(f.q,z)
                        wx=f.add(wx,z)
                src=B[j-ell] if 0<=j-ell<t else f.zero
                K[j-1]=f.sub(f.add(K[j],src),wx)
            for j in range(-6,U+2):
                v=L[U-j] if j<=U else f.zero;assert K[j]==v,(t,ell,j)
                ct['independent_top_down_bilateral_kernel_reads']+=1
                sha.update(str((t,ell,j,v)).encode())
            for n in range(1,len(L)-1):
                v=f.sub(f.mul(L[n],L[n]),f.mul(L[n-1],L[n+1]));assert f.sign(v)>=0
                ct['independent_reciprocal_root_kernel_minors']+=1
            ct['independent_unbounded_formula_QA_contexts']+=1
        if t>9:continue
        for J in models:
            d=[J[0]]+[J[n]-J[n-1] for n in range(1,len(J))]+[-J[-1]]
            e=[0]+[max(0,v) for v in d[1:]]
            assert all(e[n]**2>=e[n-1]*e[n+1] for n in range(1,len(e)-1))
            M=J.index(max(J));H=len(J)-1
            X={H:f.zero}
            for n in range(H-1,-t-1,-1):X[n]=f.mul(f.q,f.add(X[n+1],f.sc(f.one,J[n+1] if n+1>=0 else 0)))
            for ell in range(6):
                A={}
                for n in range(max(0,ell+t-1),M+1):
                    y=f.zero;src=f.zero
                    for s in range(p):y=f.add(y,X[n-s])
                    for i,b in enumerate(B):
                        k=n-ell-i
                        if 0<=k<len(J):src=f.add(src,f.sc(b,J[k]))
                    v=f.sub(y,src);A[n]=v if f.sign(v)>0 else f.zero
                for n in range(ell+t,M):
                    v=f.sub(f.mul(A[n],A[n]),f.mul(A[n-1],A[n+1]));assert f.sign(v)>=0
                    ct['independent_full_model_cut_minors']+=1
                ct['independent_cut_models_including_non_LC_J']+=1
                sha.update(str((t,ell,J,A)).encode())
    qa=json.loads((ROOT/'audit_renewal_root_primitive_cut.json').read_text());assert qa['status']=='EXACT_QA_PASS_ALL_ORDER_RENEWAL_ROOT_CUT_UNDER_PROOF_AUDIT'
    local=['renewal_root_positive_primitive_cut_proof.tex','RenewalRootPrimitiveCut.lean','RenewalRootPrimitiveCut.log',
      'audit_renewal_root_primitive_cut.py','audit_renewal_root_primitive_cut.json','verify_renewal_root_primitive_cut.py']
    deps=['GoldenPrimitiveCut.lean','GoldenPrimitiveCut.log','golden_signed_primitive_cut_closure.tex',
      'first_missing_renewal_envelope.tex']
    out=dict(status='PASS_ALL_ORDER_RENEWAL_ROOT_POSITIVE_PRIMITIVE_CUT',new_scoped_reports=9,
      kernels={'RenewalRootPrimitiveCut':reports('RenewalRootPrimitiveCut',9)},
      theorem='ALLt>=2/ell>=0: q+...+q^t=1,B_t=(1-S_t)/(1-lambda*z), finiteUIJ withpositiveprimitiveAFTERrank0LCandintervalsupport. x=future_q J,Y=[t-1]x. (Y-z^ell B_tJ)^+LCatEVERYell+t<=n<FIRSTmodeJ. Deg<=t-2 remainderinactualEABSENTonlyonthisthree-readband.',
      complete_kernel='BILATERALKhaspositiveintervalsupport(-infty,ell+t-2];reverseK=q*([t-1][ell+2]+z^(t-1))/(1-qz). ALLorders/delaysLC: bothwidthorders,smallwidths2..4,largewidthnotch>=4,rootfixedpoint,geometrictailpropagationALLpaid. No finiteentrancepremise.',
      scope='NINEcleanstandardaxiomreports forcompleteuniformscalar/CommRing/Naturalinductionkernels. Rootfactorization/reversalkernel/LCconvolution/negative-tailcutandsequenceassemblyWRITTEN,notendtoendactualcompositionformalization. GenericJneedNOTordinaryLC. Noactualsourceidentificationasserted.',
      remaining='Actual1alpha2u3r retainsEXTRAsourceP_u; doNOTidentifywholeactualresidualwithproperCIquotient. OriginalUI/generalC/fullA2OPEN. GeneralcutonlyBEFOREFIRSTJmode,notunboundedactualDmodewithoutproof.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',counts=dict(ct),QA=qa['counts'],
      independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-started,local_files=local,dependency_files=deps,
      sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'renewal_root_primitive_cut_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)
if __name__=='__main__':main()
