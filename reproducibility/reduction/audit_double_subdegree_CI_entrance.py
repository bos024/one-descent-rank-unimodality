"""Exact QA for the new h=u+2 all-padding late-C argument, pending audit."""
from pathlib import Path
from random import Random
from collections import Counter
from fractions import Fraction
from itertools import accumulate
import hashlib,json,time
from audit_degree_boundary_CI_entrance import partitions,ci
from audit_joint_structure import fastconv
from audit_binary_CI_infinite_padding_entrance import quotient,minor,convolution
from audit_arbitrary_Fibonacci_tail_late_C import add,sub,mul,power,sign,absolute
from audit_padding_three_local_prefix import primitive,positive
from verify_degree_boundary_CI_entrance import reverse_divided
from audit_subdegree_CI_entrance import geometric_inverse
from audit_mode_only_uniform_tail_closure import tail
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import rebuild
ROOT=Path(__file__).resolve().parent
Z=(0,0);Q=(-1,1);P=(0,1);PSI=(1,-1)

def padd(a,b):
    return [add(a[i] if i<len(a) else Z,b[i] if i<len(b) else Z) for i in range(max(len(a),len(b)))]
def pscale(a,c):return [mul(x,c) for x in a]
def psub(a,b):return padd(a,pscale(b,(-1,0)))
def pmul(a,b):
    c=[Z]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]=add(c[i+j],mul(x,y))
    return c
def head_polynomials():
    u=[(16,0),(1,0)];one=[(1,0)]
    q1=psub(u,[Q]);q2=psub(pscale(pmul(u,psub(u,one)),(Fraction(1,2),0)),pscale(q1,Q))
    q3=psub(pscale(pmul(pmul(u,psub(u,one)),psub(u,[(2,0)])),(Fraction(1,6),0)),pscale(q2,Q))
    out=[]
    for k,kk,tt in [(1,psub(pmul(q2,q1),q3),padd(padd(q2,pscale(q1,mul((2,0),Q))),[mul(Q,Q)])),
                    (2,psub(pmul(q2,q2),pmul(q3,q1)),padd(padd(q3,pscale(q2,mul((2,0),Q))),pscale(q1,mul(Q,Q))))]:
        p=pscale(psub(kk,pscale(tt,mul((8,0),mul(Q,Q)))),(12,0))
        assert all(Fraction(a).denominator==Fraction(b).denominator==1 for a,b in p)
        p=[(int(a),int(b)) for a,b in p]
        assert all(sign(x)>0 for x in p)
        out.append(dict(k=k,coefficients_u_minus_16=p))
    return out

def main():
    start=time.monotonic();ct=Counter();sha=hashlib.sha256();cert=set();seeds=[];rng=Random(20261029821)
    hp=head_polynomials()
    for u in range(16,91):
        qu=quotient(u)
        for s in range(2,u):
            for k in range(1,s+1):
                K=sub(mul(qu[s],qu[k]),mul(qu[s+1],qu[k-1]));T=add(add(qu[k+1] if k+1<len(qu) else Z,mul(mul((2,0),Q),qu[k])),mul(mul(Q,Q),qu[k-1]))
                assert sign(sub(K,mul(mul((8,0),power(Q,s)),T)))>=0;ct['eightfold_all_kernel_reads']+=1
            row=sub(qu[s],mul(power(Q,s),add((12*u+8,0),mul((8,0),Q))))
            assert sign(row)>=0;ct['eightfold_relaxed_row_zero']+=1
    for u in range(16,161):
        v=power(PSI,u);A=u*(u-1)//2
        for small in (3,4):
            V=[small,u+4-small];J=reverse_divided(ci(V),u);d=primitive(J)
            if small==3:
                expected=[add(( -u,0),add(mul(P,(A+2,0)),mul(mul((2,0),mul(P,P)),v))),
                    sub(add(mul(P,(u,0)),(-1,0)),mul(mul((2,0),P),v)),
                    add(Q,mul((2,0),v)),sub(add((-u-1,0),Q),mul(mul((2,0),Q),v))]
                assert d[u-1:u+3]==expected
                assert sign(sub(d[u],(3*u//2,0)))>=0 if u%2==0 else sign(sub(mul((2,0),d[u]),(3*u,0)))>=0
                assert sign(sub((u*u,0),d[u-1]))>=0 and sign(sub((1,0),d[u+1]))>=0 and sign(d[u+2])<0
            else:
                a=sub(mul((2,0),P),(1,0));b=sub((3,0),P);e=sub(mul((3,0),P),(4,0))
                expected=[sub(add(mul(P,(A+2,0)),(-u-1,0)),mul(a,v)),
                    add(add(mul(Q,(u+1,0)),(-2,0)),mul(b,v)),
                    sub(sub(P,mul(e,v)),add((A,0),mul(mul(Q,Q),(u+2,0))))]
                assert d[u:u+3]==expected
                assert sign(sub(mul((3,0),d[u]),(2*u*u,0)))>=0
                assert sign(sub((u**3,0),mul((3,0),d[u-1])))>=0
                assert sign(sub((3*u,0),mul((4,0),d[u+1])))>=0 and sign(d[u+2])<0
            ct['exact_long_endpoint_identities_and_bounds']+=1
    for u in (14,15):
        for ds in partitions(u+2):
            if len(ds)<2:continue
            V=[d+1 for d in ds];clamp=u+1;row=dict(u=u,V=V,hosts=[])
            for alpha in range(1,clamp+2):
                s=tail(V,u,alpha);g=[max(0,x) for x in s];M=g.index(max(g));margins=[]
                for n in range(1,M):
                    z=g[n]**2-g[n-1]*g[n+1];assert z>=0;cert.add(z);margins.append(z);ct['complete_small_actual_tail_minors']+=1
                row['hosts'].append(dict(alpha=alpha,first_tail_mode=M,margins=margins));ct['complete_small_hosts']+=1
                sha.update(json.dumps([u,V,alpha,s],separators=(',',':')).encode())
            seeds.append(row)
    assert len(seeds)==119
    # Every profile through u=25, and large randomly selected exact degree profiles.
    contexts=[]
    for u in range(16,26):
        contexts.extend((u,[d+1 for d in ds]) for ds in partitions(u+2) if len(ds)>=2)
    for _ in range(450):
        u=rng.randint(26,180);left=u+2;ds=[]
        while left>=4 and (not ds or rng.randrange(4)):
            d=rng.randint(2,min(left-2,max(2,left//2)));ds.append(d);left-=d
        if left>=2:ds.append(left)
        if len(ds)<2:ds=[2,u]
        contexts.append((u,[d+1 for d in sorted(ds)]))
    for u,V in contexts:
        J=reverse_divided(ci(V),u);g=positive(primitive(J));X=geometric_inverse(J);c=sub((1,0),J[0]);r=len(V);W=sum(V);w=u+r
        assert sign(c)>0 and sign(sub(mul((4,0),mul(Q,Q)),c))>=0
        assert all(sign(x)>0 for x in J[1:])
        for n in range(2,len(J)-1):assert sign(minor(J,n))>=0;ct['quotient_rank_one_tail_LC_minors']+=1
        for n in range(1,len(g)-1):assert sign(minor(g,n))>=0;ct['entire_positive_primitive_LC_minors']+=1
        ct['nonpositive_quotient_constant_contexts']+=sign(J[0])<=0
        for n in range(1,len(J)-1):
            assert sign(sub(mul(X[n],X[n]),mul(X[n-1],X[n+1])))>=0;ct['actual_infinite_tail_LC_minors']+=1
        t=V[-1];old=V[:-1];qu=quotient(u);formal=qu[:]
        while len(formal)<=u+2:formal.append(mul((-1,0),mul(Q,formal[-1])))
        B=convolution(formal,ci(old));a=mul(mul(P,P),c);d=primitive(J)
        Y=[sub(B[n] if n<len(B) else Z,mul(a,power(PSI,n))) for n in range(u+3)]
        for n in range(1,t):assert d[n]==Y[n]
        assert d[t]==sub(Y[t],(1,0)) and d[t+1]==sub(Y[t+1],B[1]),(u,V,t,d[t:t+2],Y[t:t+2]);ct['exact_source_junction_identities']+=1
        if t<=u-1:
            gap=sub(mul(B[1],B[t-1]),mul((2,0),B[t]));assert sign(sub(mul((2,0),gap),(3*u,0)))>=0
            assert sign(sub((4,0),mul((5,0),mul(a,power(Q,t-1)))))>=0;ct['uniform_junction_payments']+=1
        ee=fastconv(ci(V),[__import__('math').comb(u,j) for j in range(u+1)])
        ref=rebuild(V,W+4);xx=ref[W]-ref[W-1];yy=ref[W+1]-ref[W];amp=xx*xx+xx*yy-yy*yy
        assert yy>=xx>0 and amp>0
        for alpha in {1,2,3,rng.randint(1,u+1),u+2}:
            N=alpha+2*u+W+4;F=arm_prefix(alpha,[2]*u+V,N);D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];G=list(accumulate(F));ell=D.index(max(D))
            de0,de1=(2,2*w+1) if alpha==1 else (1,w+2) if alpha==2 else (1,w+1)
            assert F[:W]==ref[:W] and F[W]==ref[W]-de0
            assert F[W]-F[W-1]==xx-de0 and F[W+1]-F[W]==yy-de1
            seed=(xx-de0)*(xx+yy-de0)-yy*(yy-de1)
            assert seed==amp-2*de0*xx+(de1-de0)*yy+de0*de0>0;ct['exact_actual_ordinary_F_entrance_seeds']+=1
            if D[W] and D[W+1]:assert sign(sub(mul(P,(D[W],0)),(D[W+1],0)))>0
            for n in range(W+1,ell):assert D[n]**2>=D[n-1]*D[n+1];ct['actual_finite_tail_pre_mode_LC_minors']+=1
            best=1
            for n in range(4,len(F)):
                k=n-3
                if G[k]*G[best-1]<G[best]*G[k-1]:best=k
                if n>=W+1:assert G[best]*D[n-1]>=G[best-1]*D[n];ct['actual_all_shift_late_C_minimum_reads']+=1
            st=tail(V,u,alpha)
            for s in range(min(len(st),len(F)-W)):
                source_index=s-(alpha-1)
                # X_0 is C_u+1: the physical previous unit is retained.
                model=sub(X.get(s,Z),(ee[source_index] if 0<=source_index<len(ee) else 0,0))
                assert model==(st[s],0)
                assert st[s]==F[W+s]-F[W+s-1];ct['literal_actual_tail_identifications']+=1
            ct['actual_hosts']+=1
        sha.update(json.dumps([u,V,J,g],separators=(',',':')).encode());ct['quotient_contexts']+=1
    out=dict(status='EXACT_QA_DOUBLE_SUBDEGREE_UNDER_PROOF_AUDIT',counts=dict(ct),head_polynomial_coefficients=hp,
        complete_small_degree_profiles=seeds,integer_margins=sorted(cert),state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='Finite QA of a proposed UNBOUNDED h=u+2,r>=2 quotient/cut/C-entrance proof. Only 119 u=14,15 profiles are the bounded certificate; u<=13 uses an old theorem. General earlier C/A2/original UI remain OPEN; no registration yet.')
    (ROOT/'audit_double_subdegree_CI_entrance.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ('complete_small_degree_profiles','integer_margins')},ensure_ascii=False),flush=True)
    print(json.dumps(dict(small_profiles=len(seeds),integer_margins=len(cert))),flush=True)

if __name__=='__main__':main()
