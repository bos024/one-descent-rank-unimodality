"""New convex-tilt/Lagrange route to a constant-three CI entrance, pending audits."""
from pathlib import Path
from math import comb
from random import Random
from fractions import Fraction
from collections import Counter
import hashlib,json,time
from audit_arbitrary_Fibonacci_tail_late_C import add,sub,mul,power,sign
from audit_binary_CI_infinite_padding_entrance import quotient,minor,convolution
from audit_joint_structure import fastconv
from audit_degree_boundary_CI_entrance import partitions,ci
from verify_degree_boundary_CI_entrance import reverse_divided
from audit_padding_three_local_prefix import primitive,positive
from audit_mode_only_uniform_tail_closure import tail
from audit_minimum_staircase_scaled_dyadic import arm_prefix
ROOT=Path(__file__).resolve().parent
Z=(0,0);P=(0,1);Q=(-1,1)

def unrestricted(u,r,N):
    return [sum(comb(u,k)*comb(r+n-k-1,n-k) for k in range(min(u,n)+1)) for n in range(N+1)]

def main():
    started=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=Random(20261029893)
    N=55;c=[1]+[0]*N
    for n in range(1,N+1):
        c[n]=sum(c[a]*c[b]*c[n-1-a-b] for a in range(n) for b in range(n-a))
        assert c[n]==comb(3*n,n)//(2*n+1)
    w=[0]+c[1:];wp=[[1]+[0]*N]
    for k in range(1,N+1):wp.append(fastconv(wp[-1],w)[:N+1])
    basic=[(1,0),(4,-2)]
    for n in range(2,N+1):
        z=add(sub(mul(power(Q,4),(2**n,0)),mul(mul(Q,Q),(n,0))),(-4,3));basic.append(z)
        assert sign(z)>0
        if n>=3:assert sign(sub(z,basic[-2]))>0
    G=[(sum((j+1)*basic[n-2*j][0] for j in range(n//2+1)),sum((j+1)*basic[n-2*j][1] for j in range(n//2+1))) for n in range(N+1)]
    assert G[1]==(4,-2) and G[2]==(14,-7)
    for e in range(7):
        Ge=convolution(G,[comb(e,j) for j in range(e+1)])
        for k in range(2,N+1):
            composed=(sum(Ge[l][0]*wp[l][k] for l in range(k+1)),sum(Ge[l][1]*wp[l][k] for l in range(k+1)))
            j=k-1;u=3*j+e;U=unrestricted(u,4,j+1);direct=(U[j+1]+U[j-1],U[j-1]-2*U[j])
            assert composed==direct and sign(sub(direct,(26,-13)))>=0;ct['exact_Lagrange_diagonal_composition_identities']+=1
            sha.update(json.dumps([e,k,composed],separators=(',',':')).encode())
    for u in range(12,81):
        qu=quotient(u)
        for s in range(2,u-2):
            for k in range(1,s+1):
                K=sub(mul(qu[s],qu[k]),mul(qu[s+1],qu[k-1]));T=add(add(qu[k+1],mul(mul((2,0),Q),qu[k])),mul(mul(Q,Q),qu[k-1]))
                assert sign(sub(K,T))>=0;ct['unscaled_unit_interior_kernel_minors']+=1
    for u in range(12,141):
        for r in range(4,11):
            U=unrestricted(u,r,u//(r-1)+1)
            for j in range(2,u//(r-1)+1):
                curvature=(U[j+1]+U[j-1]-r,U[j-1]-2*U[j]);assert sign(curvature)>0;ct['all_rank_true_source_unit_cut_curvatures']+=1
    for _ in range(7000):
        R=rng.choice((Fraction(1,3),Fraction(2,3),Fraction(1),Fraction(3,2),Fraction(5,3),Fraction(2)))
        xm=rng.randint(1,10000);x=rng.randint(0,int(R*xm));xp=rng.randint(0,x*x//xm)
        a=Fraction(rng.randint(0,2*xm));b=a+rng.randint(0,1000);cnext=2*b-a+rng.randint(0,1000)
        em,e,ep=a,R*b,R*R*cnext
        A=[max(Fraction(0),f-z) for f,z in zip((xm,x,xp),(em,e,ep))]
        assert A[1]**2>=A[0]*A[2];ct['generic_convex_tilt_clipped_LC_triples']+=1;ct['generic_convex_tilt_all_positive']+=all(A)
    complete=[]
    for u in (14,15):
        for r in range(4,u//3+2):
            for delta in range(3,u//(r-1)+1):
                for ds in partitions(u+delta):
                    if len(ds)==r and min(ds)>=delta:complete.append((u,[d+1 for d in ds],delta))
    assert len(complete)==27
    contexts=complete[:]
    for _ in range(800):
        r=rng.randint(4,12);V=sorted(rng.choices(range(4,25),k=r));delta=rng.randint(3,V[0]-1);u=sum(t-1 for t in V)-delta
        if u<14:continue
        contexts.append((u,V,delta))
    for u,V,delta in contexts:
        r=len(V);h=sum(t-1 for t in V);W=sum(V);t=V[-1]
        assert h==u+delta and t<=u-5
        J=reverse_divided(ci(V),u);b=J[delta-1:];g=positive(primitive(b));assert all(sign(z)>0 for z in b)
        for n in range(1,len(b)-1):assert sign(minor(b,n))>=0;ct['complete_natural_quotient_LC_minors']+=1
        for n in range(2,len(g)-1):assert sign(minor(g,n))>=0;ct['complete_natural_later_primitive_LC_minors']+=1
        U=unrestricted(u,r,delta+1);E=fastconv(ci(V),[comb(u,k) for k in range(u+1)])
        assert E[:delta+1]==U[:delta+1] and U[delta+1]-E[delta+1]==V.count(delta+1)
        for j in range(2,delta+1):
            z=(E[j+1]+E[j-1],E[j-1]-2*E[j]);assert sign(z)>0;ct['literal_actual_startup_curvature_minors']+=1
        for alpha in {1,2,3,delta,rng.randint(1,max(1,u)),u+delta+2}:
            F=arm_prefix(alpha,[2]*u+V,alpha+2*u+W+4);D=[1]+[max(0,F[n]-F[n-1]) for n in range(1,len(F))];M=D.index(max(D))
            for n in range(W+1,M):assert D[n]**2>=D[n-1]*D[n+1];ct['actual_all_padding_late_D_LC_minors']+=1
            ct['actual_hosts']+=1
        sha.update(json.dumps([u,V,delta,b,g],separators=(',',':')).encode());ct['four_or_more_factor_profiles']+=1
    V=[5,29,51];u=79;alpha=1;ref=tail(V,u,250);cur=[max(0,z) for z in tail(V,u,alpha)];n=44
    relmargin=cur[n]**2*ref[n-1]*ref[n+1]-cur[n-1]*cur[n+1]*ref[n]**2
    assert cur.index(max(cur))==51 and relmargin<0 and cur[n]**2>=cur[n-1]*cur[n+1]
    out=dict(status='EXACT_QA_CONVEX_TILT_TERNARY_LAGRANGE_CONSTANT_THREE_UNDER_AUDIT',counts=dict(ct),
        small_u14_u15_profiles=[dict(u=u,V=V,delta=d) for u,V,d in complete],state_sha256=sha.hexdigest(),seconds=time.monotonic()-started,
        actual_relative_LC_negative_control=dict(u=79,V=V,alpha=1,tail_centre=44,first_tail_mode=51,margin=relmargin),
        primary_source=dict(author='Ira M. Gessel',title='Lagrange Inversion',url='https://arxiv.org/html/1609.05988',theorem='2.1.1 equation(2.1.4)',doi='10.1016/j.jcta.2016.06.018'),
        scope='Proposed UNBOUNDED analytic ALLr>=4 minimal crossing proof for ALLu>=14; u<=13 old theorem. ALL27 small contexts here are QA ONLY, not a finite entrance premise. No registration/generalC/A2/originalUI claim.')
    (ROOT/'audit_convex_tilt_Lagrange_source.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='small_u14_u15_profiles'}),flush=True)

if __name__=='__main__':main()
