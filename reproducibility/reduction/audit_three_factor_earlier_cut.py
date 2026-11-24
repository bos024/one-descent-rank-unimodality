"""Exact QA of the unbounded three-factor proof; no finite entrance premise."""
from pathlib import Path
from random import Random
from math import comb
from collections import Counter
import json,hashlib,time
from audit_arbitrary_Fibonacci_tail_late_C import add,sub,mul,power,sign
from audit_binary_CI_infinite_padding_entrance import quotient,minor,convolution
from audit_joint_structure import fastconv
from audit_degree_boundary_CI_entrance import ci
from verify_degree_boundary_CI_entrance import reverse_divided
from audit_padding_three_local_prefix import primitive,positive
from audit_minimum_staircase_scaled_dyadic import arm_prefix
ROOT=Path(__file__).resolve().parent
P=(0,1);Q=(-1,1);Z=(0,0)

def scale(a,z):return mul((a,0),z)
def unrestricted(u,r,N):
    return [sum(comb(u,k)*comb(r+n-k-1,n-k) for k in range(min(u,n)+1)) for n in range(N+1)]

def main():
    start=time.monotonic();rng=Random(202610291111);ct=Counter();sha=hashlib.sha256()
    N=48;H=[(1,0),(3,-2)]+[sub(scale(2**(n-1),(5,-3)),(2,-1)) for n in range(2,N+1)]
    G=[(sum((j+1)*H[n-2*j][0] for j in range(n//2+1)),sum((j+1)*H[n-2*j][1] for j in range(n//2+1))) for n in range(N+1)]
    assert G[1]==(3,-2) and G[2]==(10,-5) and G[3]==(24,-15) and G[4]==(57,-33)
    assert all(sign(z)>0 for n,z in enumerate(G) if n not in (1,3))
    w=[0]+[comb(3*k,k)//(2*k+1) for k in range(1,N+1)];wp=[[1]+[0]*N]
    for k in range(1,N+1):wp.append(fastconv(wp[-1],w)[:N+1])
    for k in range(3,N+1):
        val=(sum(G[l][0]*wp[l][k] for l in range(1,k+1)),sum(G[l][1]*wp[l][k] for l in range(1,k+1)))
        j=k-1;U=unrestricted(3*j,3,j+1);direct=(U[j+1]+U[j-1],U[j-1]-2*U[j])
        assert direct==val and sign(sub(direct,(3,0)))>0
        ct['signed_ternary_diagonal_composition_identities']+=1;sha.update(json.dumps([k,direct]).encode())
    for u in range(6,241):
        U=unrestricted(u,3,u//3+1)
        for j in range(2,u//3+1):
            z=(U[j+1]+U[j-1]-3,U[j-1]-2*U[j]);assert sign(z)>0
            ct['source_cone_unit_cut_margins']+=1
    for u in range(14,101):
        qv=quotient(u);s=u-2
        for k in range(1,s+1):
            K=sub(mul(qv[s],qv[k]),mul(qv[s+1],qv[k-1]))
            T=add(add(qv[k+1],scale(2,mul(Q,qv[k]))),mul(mul(Q,Q),qv[k-1]))
            assert sign(sub(K,T))>=0;ct['unscaled_penultimate_unit_kernels']+=1
        m=u//3;HN=5*2**((m+1)//2)
        assert 3*comb(u-1,m+1)>=3*(m+2)**2*HN
        for s in range(m+1,u//2+1):
            for k in range(1,s+1):
                K=sub(mul(qv[s],qv[k]),mul(qv[s+1],qv[k-1]))
                T=add(add(qv[k+1],scale(2,mul(Q,qv[k]))),mul(mul(Q,Q),qv[k-1]))
                assert sign(sub(scale(3*(m+2)**2,K),mul(qv[s],T)))>=0
                ct['earlier_cut_quantitative_ULC_kernels']+=1
    contexts=[]
    for u in range(14,24):
        for delta in range(3,u//2+1):
            h=u+delta
            for a in range(delta,h//3+1):
                for b in range(a,(h-a)//2+1):
                    c=h-a-b
                    if c<=u:contexts.append((u,[a+1,b+1,c+1],delta,True))
    for _ in range(650):
        V=sorted(rng.choices(range(4,65),k=3));delta=rng.randint(3,V[0]-1);u=sum(t-1 for t in V)-delta
        if u>=14:contexts.append((u,V,delta,False))
    for u,V,delta,complete in contexts:
        assert 2*delta<=u
        m=u//3;b=min(m,delta);L=ci(V);J=reverse_divided(L,u);g=positive(primitive(J))[b:]
        assert all(sign(z)>0 for z in J[min(m,delta-1):])
        for n in range(max(1,min(m,delta-1)+1),len(J)-1):
            assert sign(minor(J,n))>=0;ct['earlier_positive_quotient_LC_minors']+=1
        for n in range(1,len(g)-1):
            assert sign(minor(g,n))>=0;ct['earlier_complete_positive_primitive_LC_minors']+=1
        E=fastconv(L,[comb(u,n) for n in range(u+1)])
        for j in range(2,b+1):
            assert sign((E[j+1]+E[j-1],E[j-1]-2*E[j]))>0
            ct['literal_true_source_curvatures']+=1
        if delta>=m+1:
            old=ci(V[:-1]);B=convolution(quotient(u),old);c=mul(power((1,-1),u),(1,0))
            from audit_arbitrary_Fibonacci_tail_late_C import evaluate
            c=mul(c,evaluate(L,(0,-1)));a=mul((1,1),c)
            for s in range(m+1,delta+1):
                T=add(add(B[s+1],scale(2,mul(Q,B[s]))),mul(mul(Q,Q),B[s-1]))
                atom=mul(a,power(Q,s-1));atom=atom if sign(atom)>=0 else scale(-1,atom)
                assert sign(sub(minor(B,s),mul(atom,T)))>=0
                ct['actual_earlier_head_rank_one_payments']+=1
        alphas={1,2,3,b,delta,u//2+1,u+delta+2}
        for alpha in alphas:
            F=arm_prefix(alpha,[2]*u+V,alpha+2*u+sum(V)+4)
            D=[1]+[max(0,F[n]-F[n-1]) for n in range(1,len(F))];M=D.index(max(D))
            for n in range(sum(V)+1,M):
                assert D[n]**2>=D[n-1]*D[n+1];ct['actual_all_padding_late_D_LC_minors']+=1
            ct['actual_hosts']+=1
        sha.update(json.dumps([u,V,delta,b,J,g],separators=(',',':')).encode())
        ct['three_factor_profiles']+=1;ct['complete_small_profiles']+=complete
    out=dict(status='EXACT_QA_THREE_FACTOR_EARLIER_CUT_UNDER_AUDIT',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        complete_small_contexts=[dict(u=u,V=V,delta=d) for u,V,d,s in contexts if s],
        scope='All finite profiles and parameter ranges here are QA ONLY, not proof premises. Analytic source cone, earlier-cut binomial budget, quotient and primitive assembly need written and kernel verification. General C/A2/original UI remain OPEN.')
    (ROOT/'audit_three_factor_earlier_cut.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='complete_small_contexts'}),flush=True)

if __name__=='__main__':main()
