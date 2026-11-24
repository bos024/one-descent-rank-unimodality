"""Exact QA of the analytic reference theorem. NO finite proof premise."""
from pathlib import Path
from collections import Counter
from random import Random
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_mixed_binary_reference_ordinary_head import reference
from probe_binary_first_defect_ordinary_tail import arm
from audit_joint_structure import fastconv
from verify_binary_ternary_A2_original_family import core,greedy_ideal,UI,check

def at(a,n):return a[n] if 0<=n<len(a) else 0
def full_C(f,last,ct,label):
    G=[];v=0
    for z in f:v+=z;G.append(v)
    D=[max(0,z-at(f,n-1)) if n>=2 else 0 for n,z in enumerate(f)]
    kmin=1
    for n in range(4,last+1):
        k=n-3
        if G[k]*G[kmin-1]<G[kmin]*G[k-1]:kmin=k
        margin=G[kmin]*D[n-1]-G[kmin-1]*D[n]
        assert margin>=0,(label,n,kmin,margin)
        ct[label+'_full_C_minimum_ratio_checks']+=1
        ct[label+'_literal_shifts_represented']+=n-3

def main():
    start=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=Random(722071)
    for r in [57,58,59,60,61,65,79,120]:
        for s in range(0,65):
            V=[3]*r+[4]*s;f=reference(V);W=sum(V);w=len(V);A=w+3
            for n in range(A,W+1):
                assert f[n]**2>=f[n-1]*f[n+1],(r,s,n)
                ct['mixed_reference_ordinary_head_minors']+=1
            if r+3<=3*s:
                for n in range(s+4,A):
                    assert f[n]**2>=f[n-1]*f[n+1],(r,s,n)
                    ct['four_phase_earlier_ordinary_minors']+=1
            full_C(f,W+1,ct,'reference')
            ct['mixed_reference_hosts']+=1
            sha.update(str((r,s,f)).encode())
    for _ in range(360):
        V=[rng.randint(3,21) for _ in range(rng.randint(9,32))]
        f=reference(V);W=sum(V);w=len(V)
        B=[f[n]-at(f,n-1)-at(f,n-2) for n in range(W+4)]
        assert min(B)>=0 and B[W]==1 and B[W+1:]==[0]*3
        p,v=B[W-1:W-3:-1]
        assert w-1<=p<=w and 2*v>=w*(w-1)
        for n in range(W-3,W+1):
            assert f[n]**2>=f[n-1]*f[n+1],(V,n)
            ct['arbitrary_order_terminal_ordinary_minors']+=1
        ct['arbitrary_order_terminal_hosts']+=1
        sha.update(str((V,f[W-4:W+3],B[W-2:W+1])).encode())
    for r in [57,60,79]:
        for s in [1,2,9,20,30]:
            h=2*r+3*s
            for u in [h-5,h-4,h-3,h-2,h,h+7]:
                for alpha in [1,2,5]:
                    f=arm(alpha,[2]*u+[3]*r+[4]*s)
                    full_C(f,len(f)-2,ct,'actual_dense')
                    ct['actual_dense_hosts']+=1
                    sha.update(str((alpha,u,r,s,f)).encode())
    # ORIGINAL coefficients use actual dense new arms and arbitrary A8 arms.
    for case in range(18):
        r=57+case%3;s=1+case%4;u=2*r+3*s-5+case%3;alpha=1+case%3
        X=arm(alpha,[2]*u+[3]*r+[4]*s)[:-2]
        beta=1+case%2;V=([2]*(case%4)+[3]*(case%5)) if case%2 else [3]*(case%4)+[4]*(case%5)
        Y=arm(beta,V)[:-2]
        check(X,Y,ct,sha,bool(V))
        M=5+case%5;H,L,R=core(X,Y,M)
        host=[1]*alpha+[2]*u+[3]*r+[4]*s+[M]+list(reversed([1]*beta+V))
        actual=greedy_ideal(host)
        assert actual==H and UI(actual)
        ct['true_greedy_ORIGINAL_new_dense_family']+=1
        ct['true_greedy_ORIGINAL_rank_counts']+=len(actual)
        sha.update(str((host,actual)).encode())
    out=dict(status='PASS_EXACT_QA_MIXED_BINARY_REFERENCE_DIRECT_ORDINARY_AND_DENSE_ORIGINAL',
        counts=dict(ct),sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='Finite QA ONLY. Universal theorem uses analytic scalar/window/damping proofs, NO finite entrance premise. General original conjecture remains OPEN.')
    (ROOT/'audit_mixed_binary_reference_ordinary.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)
if __name__=='__main__':main()
