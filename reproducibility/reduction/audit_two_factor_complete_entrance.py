"""Exact audits of the proposed complete late-D-LC entrance, with its actual finite premise."""
from pathlib import Path
from random import Random
from math import comb
from collections import Counter
import json,hashlib,time
from audit_arbitrary_Fibonacci_tail_late_C import add,sub,mul,power,sign
from audit_joint_structure import fastconv
from audit_degree_boundary_CI_entrance import ci
from verify_degree_boundary_CI_entrance import reverse_divided
from audit_padding_three_local_prefix import primitive,positive
from audit_binary_CI_infinite_padding_entrance import minor,quotient
from audit_mode_only_uniform_tail_closure import tail
from audit_minimum_staircase_scaled_dyadic import arm_prefix
ROOT=Path(__file__).resolve().parent
Z=(0,0);Q=(-1,1)

def det(A,n):return A[n]**2-A[n-1]*A[n+1]
def mode_field(g):
    M=0
    for n in range(1,len(g)):
        if sign(sub(g[n],g[M]))>0:M=n
    return M
def intminor(Qv,n,k):
    K=sub(mul(Qv[n],Qv[k]),mul(Qv[n+1],Qv[k-1]))
    T=add(add(Qv[k+1],mul((2,0),mul(Q,Qv[k]))),mul(mul(Q,Q),Qv[k-1]))
    return K,T

def main():
    start=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=Random(202610291151)
    N=48
    h=[(1,0),(2,-2)]
    for n in range(2,N+1):
        h.append(( (10*3**(n-1)+2*(-1)**n)//4,(-5*3**(n-1)+3*(-1)**n)//4))
        assert (10*3**(n-1)+2*(-1)**n)%4==0 and (-5*3**(n-1)+3*(-1)**n)%4==0
        assert sign(h[-1])>0
    G=[(sum((j+1)*h[n-2*j][0] for j in range(n//2+1)),sum((j+1)*h[n-2*j][1] for j in range(n//2+1))) for n in range(N+1)]
    assert G[1]==(2,-2) and G[2]==(10,-3) and G[3]==(26,-16)
    assert all(sign(z)>=0 for n,z in enumerate(G) if n!=1)
    w=[0]+[comb(4*k,k)//(3*k+1) for k in range(1,N+1)];wp=[[1]+[0]*N]
    for k in range(1,N+1):wp.append(fastconv(wp[-1],w)[:N+1])
    for k in range(N+1):
        left=11*wp[2][k]-4*w[k]+4*(k==1)+5*(k==2)
        right=sum(v*wp[l-1][k-2] for l,v in enumerate([0,0,0,100,340,546,504,276,84,11]) if l>=3) if k>=2 else 0
        assert left==right and left>=0;ct['exact_quaternary_pair_coefficient_identities']+=1
    for k in range(3,N+1):
        z=(sum(G[l][0]*wp[l][k] for l in range(1,k+1)),sum(G[l][1]*wp[l][k] for l in range(1,k+1)))
        j=k-1;u=4*j
        U=[sum(comb(u,i)*(n-i+1) for i in range(min(n,u)+1)) for n in range(j+2)]
        assert z==(U[j+1]+U[j-1],U[j-1]-2*U[j]) and sign(sub(z,(2,0)))>0
        ct['quaternary_signed_diagonal_identities']+=1;sha.update(json.dumps([k,z]).encode())
    for u in range(24,181):
        m=u//4
        assert 2*4**m*comb(4*m-1,m+1)>=(m+2)**2*17**m
        assert 3*89*(u+1)*(u-1)*(u-2)>=66*(u+2)**2*(3*u+2)
        qv=quotient(u)
        for s in range(m+1,u//2+1):
            for k in (1,s//2+1,s):
                K,T=intminor(qv,s,k)
                assert sign(sub(mul((4*(m+2)**2,0),K),mul(qv[s],T)))>=0
                ct['left_half_earlier_cut_kernel_payments']+=1
    finite=[];margins=set()
    for u in range(14,24):
        for A in range(4,u-2):
            for B in range(A,u-2):
                delta=A+B-2-u
                if 3<=delta<=A-1:finite.append((u,[A,B],delta))
    assert len(finite)==245
    for u,V,delta in finite:
        h=u+delta
        for alpha in range(1,(u+h)//2+2):
            D=[max(0,z) for z in tail(V,u,alpha)];M=D.index(max(D))
            for n in range(1,M):
                z=det(D,n);assert z>=0;margins.add(z);ct['finite_entrance_integer_comparisons']+=1
            ct['finite_entrance_hosts']+=1
        sha.update(json.dumps([u,V,delta,D],separators=(',',':')).encode())
    for u in list(range(14,46))+[64,100,150,240]:
        for c in (-1,0,1,2):
            B=u-c;K=c+3
            for alpha in {1,2,3,K,u//2,u+2}:
                f=tail([B],u,alpha);fp=[max(0,z) for z in f];M=fp.index(max(fp))
                if M>K:
                    for i in range(1,K+1):
                        assert f[i]*f[K]>=f[i-1]*f[K+1];ct['long_boundary_actual_prefix_ratio_comparisons']+=1
                for n in range(K,M):assert det(fp,n)>=0;ct['long_boundary_old_one_jump_LC_minors']+=1
                if c==-1:
                    assert (f[1]+f[2])**2>=(f[0]+f[1])*(f[2]+f[3]);ct['long_boundary_two_window_seed_minors']+=1
                for A in {K,max(4,K),K+1,(K+B)//2,B}:
                    if A<2 or A>B:continue
                    win=[max(0,sum(f[n:n+A])) for n in range(len(f))];mode=win.index(max(win))
                    for n in range(1,mode):assert det(win,n)>=0;ct['long_boundary_transported_window_minors']+=1
                    ct['long_boundary_transported_hosts']+=1
    contexts=[]
    for _ in range(1600):
        V=sorted(rng.choices(range(4,100),k=2));delta=rng.randint(3,V[0]-1);u=sum(t-1 for t in V)-delta
        if u>=24 and max(V)<=u-3:contexts.append((u,V,delta))
    for u,V,delta in contexts:
        J=reverse_divided(ci(V),u);b=min(u//4,delta);g=positive(primitive(J))[b:]
        for n in range(1,len(g)-1):
            assert sign(minor(g,n))>=0;ct['regular_cone_full_earlier_primitive_LC_minors']+=1
        for alpha in {1,2,3,b,delta,u//2,u+delta+2}:
            D=[max(0,z) for z in tail(V,u,alpha)];M=D.index(max(D))
            for n in range(1,M):assert det(D,n)>=0;ct['regular_cone_actual_late_D_LC_minors']+=1
            ct['regular_cone_actual_hosts']+=1
        ct['regular_cone_CI_profiles']+=1;sha.update(json.dumps([u,V,delta,g],separators=(',',':')).encode())
    out=dict(status='EXACT_QA_COMPLETE_TWO_FACTOR_LATE_D_LC_ENTRANCE_UNDER_AUDIT',counts=dict(ct),
        finite_entrance_profiles=[dict(u=u,V=V,delta=d) for u,V,d in finite],integer_margins=sorted(margins),
        state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='ONLY the complete245 regular profilesu14..23 with ALL analytic-clamp padding hosts are finite theorem premises. ALL other finite ranges/random contexts are QA ONLY. Unbounded long-boundary window transport, regular u>=24 binomial kernel budgets, source cone and old assembly require written/kernel verification. Original C/A2/UI OPEN.')
    (ROOT/'audit_two_factor_complete_entrance.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ('finite_entrance_profiles','integer_margins')}),flush=True)

if __name__=='__main__':main()
