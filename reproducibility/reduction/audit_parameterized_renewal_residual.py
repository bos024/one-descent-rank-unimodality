"""Exact QA only. All-order proofs are symbolic and have no finite premise."""
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
import sys,json,time,hashlib,random
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_renewal_root_primitive_cut import ReciprocalRing

def counts(t,N):
    h=[1];s=1
    for n in range(1,N+1):
        h.append(s);s+=h[-1]
        if n>=t:s-=h[n-t]
    return h
def power(f,a,m):
    v=f.one
    for _ in range(m):v=f.mul(v,a)
    return v
def conv(a,b,N):
    return [sum(a[i]*b[n-i] for i in range(max(0,n-len(b)+1),min(n,len(a)-1)+1)) for n in range(N+1)]
def numerator(t,V):
    P=[1]+[-1]*t;N=[1]
    for v in V:
        S=[0]+[1]*v
        N=conv(S,N,len(S)+len(N)-2)
        for i,p in enumerate(P):N[i]+=p
        assert N[0]==1 and N[1:t+1]==[0]*t and min(N)>=0
    return N
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=random.Random(110102)
    for t in list(range(3,61))+[100,250]:
        N=240 if t<100 else 2*t+20;h=counts(t,N+1)
        top=Q(2)-Q(1,2**(t-1))
        thetas=[Q(1),Q(3,2),Q(8,5),top-Q(1,2**(t+1)),top-Q(1,2**(2*t))]
        for θ in thetas:
            if θ>=top:continue
            p=(2-θ)*2**(t-2);b=2*p-1;C=θ+max(Q(1),(θ-1)**2/b)
            K=[h[n]-θ*(h[n-1] if n else 0) for n in range(N+2)]
            for n in range(3,N+1):
                assert K[n-1]>0
                M=K[n]**2-K[n-1]*K[n+1];assert abs(M)<=C*K[n-1],(t,θ,n)
                ct['rational_parameter_ALLorder_minor_reads']+=1
            assert K[t]==p and K[t+1]==b
            assert K[t+1]**2-K[t]*K[t+2]==1-(1+θ)*p
            assert K[t+2]**2-K[t+1]*K[t+3]==θ*b+(θ-1)**2
            ct['parameter_complete_boundary_contexts']+=1
            sha.update(str((t,θ,C,K[-2:])).encode())
    print(json.dumps(dict(phase='rational_parameter_complete',counts=dict(ct))),flush=True)
    for t in range(3,13):
        f=ReciprocalRing(t-1);θ=f.l;h=counts(t,125)
        p=f.sc(f.sub(f.sc(f.one,2),θ),2**(t-2));b=f.sub(f.sc(p,2),f.one)
        assert f.sign(b)>0
        sq=power(f,f.sub(θ,f.one),2);m=b if f.sign(f.sub(b,sq))>=0 else sq
        Cb=f.add(f.mul(θ,b),m)
        K=[f.sub(f.sc(f.one,h[n]),f.sc(θ,h[n-1] if n else 0)) for n in range(len(h))]
        for n in range(3,len(K)-1):
            assert f.sign(K[n-1])>0
            M=f.sub(power(f,K[n],2),f.mul(K[n-1],K[n+1]));bound=f.mul(Cb,K[n-1])
            assert f.sign(f.sub(bound,f.mul(b,M)))>=0 and f.sign(f.add(bound,f.mul(b,M)))>=0
            ct['EXACTadjacent_root_parameter_minor_reads']+=1
        sha.update(str((t,b,Cb,K[t+1])).encode())
    print(json.dumps(dict(phase='adjacent_roots_complete',counts=dict(ct))),flush=True)
    for t in range(2,10):
        f=ReciprocalRing(t);Nmax=95;h=counts(t,Nmax)
        weights=[power(f,f.q,t-i+1) for i in range(1,t+1)]
        U=[f.one]
        for n in range(1,Nmax+1):
            v=f.zero
            for i,a in enumerate(weights,1):
                if i<=n:v=f.add(v,f.mul(a,U[n-i]))
            U.append(v)
        contexts=[[],[t],[t+1],[t+3,t],sorted(rng.choices(range(t,t+7),k=3))]
        contexts += [None]
        for V in contexts:
            P=numerator(t,V) if V is not None else [rng.randint(0,4) for _ in range(12)]
            F=conv(P,h,Nmax);G=[];s=0
            for v in F:s+=v;G.append(s)
            for n in range(1,Nmax+1):
                gap=f.sub(f.sc(f.one,G[n]),f.sc(f.l,G[n-1]))
                expected=f.zero
                for i,a in enumerate(P):
                    if i<=n:expected=f.add(expected,f.sc(U[n-i],a))
                assert gap==expected
                ct['positive_numerator_cumulative_root_gap_reads']+=1
            for r in [2,3,4,t+1,2*t+3]:
                rho=f.mul(power(f,f.l,r-2),power(f,f.sub(f.l,f.one),2))
                B=[f.zero]*(max(t,r-1)+1)
                for i in range(2,t+1):B[i]=weights[i-1]
                for k in range(2,r):B[k]=f.add(B[k],f.mul(power(f,f.l,k-2),power(f,f.sub(f.l,f.one),2)))
                mass=f.mul(f.sub(f.l,f.one),power(f,f.l,r-2));actualmass=f.zero
                for z in B:actualmass=f.add(actualmass,z)
                assert actualmass==mass
                BU=[]
                for n in range(Nmax+1):
                    z=f.one if n==0 else f.zero
                    for k,b in enumerate(B):
                        if k<=n:z=f.add(z,f.mul(b,U[n-k]))
                    BU.append(z)
                for n in range(Nmax+1):
                    R=f.sub(f.sc(f.one,F[n]-(F[n-1] if n else 0)),f.sc(rho,G[n-r] if n>=r else 0))
                    rhs=f.zero
                    for i,a in enumerate(P):
                        if i<=n:rhs=f.add(rhs,f.sc(BU[n-i],a))
                    atom=P[n] if n<len(P) else 0
                    upper=f.add(f.sc(f.one,atom),f.sc(mass,sum(P[:max(0,n-1)])))
                    assert R==rhs and f.sign(f.sub(R,f.sc(f.one,atom)))>=0 and f.sign(f.sub(upper,R))>=0,(t,V,r,n)
                    ct['ALLdelay_EXACTpositive_coupled_identity_and_two_sided_reads']+=1
            ct['positive_numerator_contexts']+=1
            sha.update(str((t,V,P,F[-3:])).encode())
        print(json.dumps(dict(order=t,phase='positive_coupled_source',reads=ct['ALLdelay_EXACTpositive_coupled_identity_and_two_sided_reads'])),flush=True)
    out=dict(status='EXACT_QA_PASS_PARAMETERIZED_RESIDUAL_AND_ALL_DELAY_POSITIVE_COUPLED_SOURCE',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      scope='ALLsymbolicproofs haveNOnewfinitepremise. ParameterenvelopeincludesADJACENTrootsofthepreviousorder. ALLdelaypositivecoupledlowerboundNOTmonotonicity,CDFgrowthNOTcoefficientUI. Generaloriginal/C/A2andmixed3/4remainOPEN.')
    (ROOT/'audit_parameterized_renewal_residual.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
