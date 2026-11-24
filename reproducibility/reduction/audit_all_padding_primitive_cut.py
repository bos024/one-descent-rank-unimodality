"""Exact QA of the primitive-cut identity, startup and all-padding actual assembly."""
from pathlib import Path
from math import ceil
from random import Random
from collections import Counter
from itertools import accumulate,combinations_with_replacement
import json,hashlib,time
from audit_joint_structure import fastconv
from audit_arbitrary_Fibonacci_tail_late_C import add,sub,mul,power,sign
from audit_binary_CI_infinite_padding_entrance import minor
from probe_divided_CI_positive_primitive import divided
from probe_finite_padding_geometric_deficit import arrays
from audit_padding_three_local_prefix import primitive,positive
from audit_minimum_staircase_scaled_dyadic import arm_prefix
Q=(-1,1);PHI=(0,1);PSI=(1,-1);ZERO=(0,0);ONE=(1,0)

def K(a,j):return power(Q,-j) if j<0 else Q if j<a else power(Q,3) if j==a else ZERO
def scale(k,x):return mul((k,0),x)

def main():
    start=time.monotonic();rng=Random(20261029759);ct=Counter();sha=hashlib.sha256();small=[];integer_margins=set()
    # Complete w=u+len(V)<8 exceptions, and the exact old large-padding clamp.
    for u in range(3,7):
        for length in range(1,4):
            if u+length>=8:continue
            for V in combinations_with_replacement(range(3,7),length):
                h=sum(t-1 for t in V)
                if h>u-1:continue
                m=u-1;clamp=(m+h+1)//2
                for alpha in range(1,clamp+1):
                    _,_,_,raw,A,_=arrays(V,m,alpha);ell=A.index(max(A));margins=[]
                    for n in range(m,ell+1):
                        M=A[n]**2-A[n-1]*A[n+1];assert M>=0
                        margins.append(M);integer_margins.add(M);ct['complete_small_actual_pre_mode_LC_minors']+=1
                    small.append(dict(u=u,V=list(V),alpha=alpha,clamp=clamp,first_A_mode=ell,margins=margins))
    for trial in range(1200):
        V=sorted(rng.choices(range(3,31),k=rng.randint(1,8)));h=sum(t-1 for t in V)
        u=h+1+(0 if trial%3 else rng.randint(1,8));m=u-1;r=len(V);W=h+r
        alpha=rng.randint(1,h+4);a=alpha-1
        L,Cinf,E,raw,Aseq,_=arrays(V,m,alpha);_,b=divided(L,u);d=primitive(b)+[sub(ZERO,b[-1])]
        M=0
        for n in range(1,len(b)):
            if sign(sub(b[n],b[M]))>0:M=n
        assert all(sign(d[k])<=0 for k in range(M+1,len(d)))
        dp=positive(d)
        for n in range(2,len(dp)-1):assert sign(minor(dp,n))>=0
        x=[ZERO]*(len(b)+1)
        for n in range(len(b)-1,-1,-1):x[n]=mul(Q,add(x[n+1],b[n+1] if n+1<len(b) else ZERO))
        for n in range(len(x)):
            assert x[n]==(Cinf[u+n] if u+n<len(Cinf) else 0,0)
            ct['exact_right_geometric_actual_Cinf_identifications']+=1
        Estar=[add(b[n] if n<len(b) else ZERO,mul(Q,b[n-1] if n else ZERO)) for n in range(len(b)+1)]
        c0=sub((E[0],0),Estar[0])
        for n in range(1,len(E)):assert Estar[n]==(E[n],0)
        T=ZERO
        for k in range(M+1,len(d)):T=add(T,mul(power(Q,k),sub(ZERO,d[k])))
        assert sign(T)>=0
        Fs={};Ac={}
        for n in range(a+1,M+1):
            F=ZERO
            for k in range(1,M+1):
                if sign(d[k])>0:F=add(F,mul(K(a,n-k),d[k]))
            Fs[n]=F
            source=Estar[n-a] if 0<=n-a<len(Estar) else ZERO
            generic=sub(x[n],source);expected=sub(F,mul(T,power(PHI,n)))
            assert mul(power(Q,2),generic)==expected
            actualraw=(raw[u+n] if u+n<len(raw) else 0,0)
            assert actualraw==generic
            Ac[n]=generic if sign(generic)>0 else ZERO
            ct['exact_signed_primitive_convolution_and_constant_cut_identities']+=1
        for n in range(a+2,M):
            assert sign(minor([Fs[n-1],Fs[n],Fs[n+1]],1))>=0
            assert sign(minor([Ac[n-1],Ac[n],Ac[n+1]],1))>=0
            ct['exact_generic_cut_LC_after_deleted_initial_primitive']+=1
        ell=Aseq.index(max(Aseq))
        for n in range(m,ell+1):
            assert Aseq[n]**2>=Aseq[n-1]*Aseq[n+1]
            ct['exact_actual_all_padding_through_first_mode_LC_minors']+=1
        if u+r>=8:
            off=u+a;w=u+r;E2=E[2]
            assert 2*E2==w*w-u+r and 2*E2>=w*(w-1)
            def C(n):return Cinf[n] if 0<=n<len(Cinf) else 0
            for n in [off,off+1]:
                if n>=len(Cinf)-1 or C(n-1)<=0:continue
                if n==off:
                    value=(C(n)-1)**2-C(n-1)*(C(n+1)-w)
                    assert value==C(n)**2-C(n-1)*C(n+1)-2*C(n)+1+C(n-1)*w
                else:
                    value=(C(n)-w)**2-(C(n-1)-1)*(C(n+1)-E2)
                    assert value==C(n)**2-C(n-1)*C(n+1)+C(n-1)*E2-2*w*C(n)+C(n+1)+w*w-E2
                assert value>0;ct['exact_uniform_first_source_startup_minors']+=1
        Tact=2*u+W+alpha;F=arm_prefix(alpha,[2]*u+V,Tact+5);G=list(accumulate(F))
        Dact=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
        assert Dact.index(max(Dact))==r+2+ell
        best=1
        for N in range(4,Tact+2):
            k=N-3
            if G[k]*G[best-1]<G[best]*G[k-1]:best=k
            if N>=W+1:
                assert G[best]*Dact[N-1]>=G[best-1]*Dact[N]
                ct['exact_all_padding_all_read_prefix_minimum_C_payments']+=1
        ct['actual_all_padding_CI_contexts']+=1
        sha.update(json.dumps([V,u,alpha,b,raw,Aseq,M,T],separators=(',',':')).encode())
    out=dict(status='PASS_EXACT_QA_SIGNED_PRIMITIVE_CUT_AND_ALL_PADDING_ACTUAL_LATE_C',counts=dict(ct),
        complete_small_actual_contexts=small,complete_small_actual_integer_margins=sorted(integer_margins),
        state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='Independent exact QA of a NEW written universal cut theorem and all-padding actual assembly, contingent on repaired later-primitive theorem and formal audits. Complete small-startup exception enumeration with old analytic alpha-clamp. No earlier reference C, shorter binary counts, general C/A2/original UI claim.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['complete_small_actual_contexts','complete_small_actual_integer_margins']}),flush=True)

if __name__=='__main__':main()
