"""Exact arbitrary-degree renewal-root QA; no floating/root-irreducibility assumption."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from math import comb
import json,time,hashlib
ROOT=Path(__file__).resolve().parent
class RootField:
    def __init__(self,t):
        self.t=t;self.zero=(0,)*t;self.one=(1,)+(0,)*(t-1);self.q=(0,1)+(0,)*(t-2);self.intervals={}
    def add(self,a,b):return tuple(x+y for x,y in zip(a,b))
    def sub(self,a,b):return tuple(x-y for x,y in zip(a,b))
    def scale(self,a,k):return tuple(k*x for x in a)
    def qmul(self,a):
        z=a[-1];return(z,)+tuple(a[j-1]-z for j in range(1,self.t))
    def mul(self,a,b):
        p=[0]*(2*self.t-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):p[i+j]+=x*y
        for k in range(len(p)-1,self.t-1,-1):
            z=p[k];p[k-self.t]+=z
            for j in range(1,self.t):p[k-self.t+j]-=z
        return tuple(p[:self.t])
    def power(self,k):
        x=self.one
        for _ in range(k):x=self.qmul(x)
        return x
    def root_value(self,n,M):
        v=1;s=1
        for k in range(self.t-1,-1,-1):
            s*=M;v=v*n+(-1 if k==0 else 1)*s
        return v
    def interval(self,bits):
        if bits not in self.intervals:
            M=1<<bits;lo=0;hi=M
            while hi-lo>1:
                mid=(lo+hi)//2
                if self.root_value(mid,M)<0:lo=mid
                else:hi=mid
            self.intervals[bits]=(lo,hi,M)
        return self.intervals[bits]
    def sign(self,v):
        if v==self.zero:return 0
        bits=max(128,((4*max(abs(a).bit_length() for a in v)+100+127)//128)*128)
        while bits<=8192:
            n,N,M=self.interval(bits);lo=hi=v[-1];s=1
            for a in reversed(v[:-1]):
                s*=M;terms=[lo*n,lo*N,hi*n,hi*N];lo=min(terms)+a*s;hi=max(terms)+a*s
            if lo>0:return 1
            if hi<0:return -1
            bits*=2
        raise ArithmeticError('Exact sign remains unresolved; no irreducibility/zero claim inferred.')
def product_intervals(p,h):return [max(0,min(p-1,n)-max(0,n-h+1)+1) for n in range(p+h-1)]
def convolution(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out
def main():
    start=time.monotonic();ct=Counter();sha=hashlib.sha256()
    for p in range(2,22):
        for h in range(2,p+1):
            for q in [F(1,2),F(11,20),F(3,5),F(5,8),F(2,3)]:
                g=product_intervals(p,h);g[p]+=1;v=F(0);seq=[]
                for n in range(len(g)+3):v=q*v+(g[n] if n<len(g) else 0);seq.append(v)
                assert all(seq[n]**2>=seq[n-1]*seq[n+1] for n in range(1,len(seq)-1))
                ct['EXACT_rational_all_width_notch_profiles']+=1
    for t in range(2,17):
        Fq=RootField(t);p=t-1
        widths=list(range(2,23)) if t<=10 else [2,3,4,5,8,12,20,35]
        for h in widths:
            ell=h-2;U=ell+t-2;g=product_intervals(p,h);g[p]+=1
            seq=[];v=Fq.zero
            for n in range(len(g)+5):
                v=Fq.add(Fq.qmul(v),Fq.scale(Fq.one,g[n] if n<len(g) else 0));seq.append(v)
            assert all(Fq.sign(v)>0 for v in seq)
            for n in range(1,len(seq)-1):
                minor=Fq.sub(Fq.mul(seq[n],seq[n]),Fq.mul(seq[n-1],seq[n+1]));assert Fq.sign(minor)>=0,(t,h,n,minor)
                ct['EXACT_renewal_root_LC_minors']+=1
            B=[]
            for i in range(t):
                b=Fq.zero
                for k in range(1,t-i+1):b=Fq.add(b,Fq.power(k))
                B.append(b)
            assert B[0]==Fq.one
            for j in range(-4,U+4):
                idx=U-j;K=Fq.qmul(seq[idx]) if 0<=idx<len(seq) else Fq.zero
                direct=Fq.zero
                for s in range(p):direct=Fq.add(direct,Fq.power(max(1,s-j)))
                source=Fq.zero
                if j>=ell:
                    for i in range(min(t-1,j-ell)+1):source=Fq.add(source,B[i])
                direct=Fq.sub(direct,Fq.sub(source,Fq.qmul(source)))
                assert Fq.sub(K,Fq.qmul(K))==direct,(t,h,j)
                ct['EXACT_bilateral_kernel_and_source_identity_reads']+=1
            ct['EXACT_algebraic_root_profiles']+=1
            sha.update(str((t,h,seq[-3:],B)).encode())
    asymmetric=[];v=F(0)
    for n in range(29):v=F(comb(28,n))-v/2;asymmetric.append(v)
    asymmetric=[int(v*(2**28)) for v in asymmetric]
    for j in range(4):asymmetric=convolution(asymmetric,[1]*5)
    for J in [[comb(36,n) for n in range(37)],asymmetric]:
        d=[max(0,v-(J[n-1] if n else 0)) for n,v in enumerate(J)]
        assert all(d[n]**2>=d[n-1]*d[n+1] for n in range(1,len(d)-1))
        mode=J.index(max(J));H=len(J)-1
        for t in range(2,11):
            fq=RootField(t);B=[]
            for i in range(t):
                v=fq.zero
                for k in range(1,t-i+1):v=fq.add(v,fq.power(k))
                B.append(v)
            X={H:fq.zero}
            for n in range(H-1,-t-1,-1):X[n]=fq.qmul(fq.add(X[n+1],fq.scale(fq.one,J[n+1] if n+1>=0 else 0)))
            for ell in range(7):
                values={}
                for n in range(max(0,ell+t-1),mode+1):
                    y=fq.zero
                    for i in range(t-1):y=fq.add(y,X[n-i])
                    source=fq.zero
                    for i,b in enumerate(B):
                        k=n-ell-i
                        if 0<=k<len(J):source=fq.add(source,fq.scale(b,J[k]))
                    v=fq.sub(y,source);values[n]=v if fq.sign(v)>0 else fq.zero
                for n in range(ell+t,mode):
                    minor=fq.sub(fq.mul(values[n],values[n]),fq.mul(values[n-1],values[n+1]))
                    assert fq.sign(minor)>=0,(t,ell,n)
                    ct['EXACT_FULL_cut_model_LC_minors']+=1
                ct['EXACT_nonsymmetric_or_binomial_cut_models']+=1
                sha.update(str((J,t,ell,mode,values)).encode())
    out=dict(status='EXACT_QA_PASS_ALL_ORDER_RENEWAL_ROOT_CUT_UNDER_PROOF_AUDIT',counts=dict(ct),
      state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
      scope='QAONLY, writtenproofALLt>=2/ell>=0NOcountbound. ExactZ[q]/(q+...+q^t-1)withINTEGERisolatingintervalsigns;noirreducibilityassumption/noFLOAT;zeroonlyexactresiduezero. RationalnotchcasesINDEPENDENTofrootconstraintwhenh<=p.')
    (ROOT/'audit_renewal_root_primitive_cut.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
