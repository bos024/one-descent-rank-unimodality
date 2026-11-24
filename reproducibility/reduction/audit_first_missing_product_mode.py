"""Exact QA for two UNBOUNDED analytic results; no new finite proof premise."""
from pathlib import Path
from random import Random
from collections import Counter
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_binary_first_defect_ordinary_tail import arm
from audit_joint_structure import fastconv
from verify_binary_ternary_A2_original_family import UI
def at(p,n):return p[n] if 0<=n<len(p) else 0
def window(E,t):
    out=[];v=0
    for n in range(len(E)+t-1):v+=at(E,n)-at(E,n-t);out.append(v)
    return out
def main():
    st=time.monotonic();rng=Random(9518072);ct=Counter();sha=hashlib.sha256()
    for _ in range(800):
        k=rng.randint(6,90);delta=rng.randint(0,k)
        U=[rng.randint(0,8) for _ in range(rng.randint(1,20))];U[0]=rng.randint(1,8)
        A=[1,1,2]+U
        Q=[1]+[2**(j-1) for j in range(1,k)]+[2**(k-1)-delta,rng.randint(1,30),rng.randint(1,30)]
        H=fastconv(A,Q)
        for n in [k,k+1,k+2]:
            loss=0 if n<=k+1 else delta-2**(k-3)
            assert H[n]-H[n-1]>=Q[n]-loss>0
            ct['generic_whole_polynomial_three_increase_margins']+=1
    for k in range(6,41):
        for kind in range(12):
            if kind%3==0:V=[k-1]*(k-2+kind//6)
            elif kind%3==1:V=list(range(2,k))
            else:V=sorted(rng.randint(k,k+15) for _ in range(k-2))
            beta=rng.randint(1,9);Y=arm(beta,V)[:-2];b=len(Y)-1
            assert next(j for j in range(1,k+1) if at(Y,j)<2**(j-1))==k
            alpha=rng.randint(1,15);U=sorted(rng.randint(2,35) for _ in range(rng.randint(1,18)))
            X=arm(alpha,U)[:-2];a=len(X)-1;H=fastconv(X,Y);delta=2**(k-1)-Y[k]
            assert 1<=delta<=k
            for n in [k,k+1,k+2]:
                assert H[n]>H[n-1];ct['actual_three_first_missing_product_increases']+=1
            assert UI(H)
            mu=H.index(max(H));nu=a+b-mu;assert mu>=k+2 and nu<=a+b-k-2
            ct['actual_unbounded_product_mode_bounds']+=1
            sha.update(str((alpha,U,beta,V,H[k-1:k+3],mu)).encode())
    for k in range(6,61):
        Y=arm(1,[k-1]*(k-2))[:-2];b=len(Y)-1
        assert 2**(k-1)-Y[k]==3
        for alpha,s in [(1,2),(1,3),(2,3),(3,4),(1,k),(k,2)]:
            X=arm(alpha,[s])[:-2];a=len(X)-1;p=fastconv(X[::-1],Y[::-1])
            E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
            d=[max(0,x-at(p,n-1)) for n,x in enumerate(p)];assert UI([x<<n for n,x in enumerate(d)])
            if a+3<=k:
                m=min(alpha+1,s);L=b+a-k+1;R=b+m-1
                assert E[L]==3 and UI(E[:L+1]) and min(E[:L+1])>=1
                assert E[L+1:b]==[0]*(b-L-1) and E[b:R+1]==[1]*m
                assert max(E[R+1:],default=0)<=0
                assert len(p)-1-p[::-1].index(max(p))<=L-3
                ct['entire_unbounded_one_part_exceptional_profiles']+=1
            else:assert UI([max(0,x) for x in E])
            for t in sorted(set([k-3,k-2,max(k-3,b-a),b+1])):
                W=[max(0,x) for x in window(E,t)];assert UI(W)
                pos=[j for j,x in enumerate(W) if x>0];assert pos==list(range(pos[-1]+1))
                ct['entire_unbounded_one_part_source_windows']+=1
        X=arm(1,[2])[:-2];p=fastconv(X[::-1],Y[::-1]);E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
        assert window(E,k-4)[b-1:b+2]==[3,1,2];ct['actual_all_kappa_shorter_window_counterexamples']+=1
    out=dict(status='PASS_EXACT_QA_FIRST_MISSING_PRODUCT_MODE_AND_UNBOUNDED_ONE_PART_WINDOWS',
        counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
        scope='ALLfiniteproducts/windowsQAONLY;NONEfiniteproofpremises. OnepartwindowTHEOREMretainsFULLCofYandFULL_OLD_A2;generaloriginalOPEN.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
