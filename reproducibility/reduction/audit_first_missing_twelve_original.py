"""Actual-model QA ONLY. The finite proof certificate is a separate exhaustive artifact."""
from pathlib import Path
from collections import Counter
from random import Random
import sys,time,json,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_joint_structure import fastconv
from probe_binary_first_defect_ordinary_tail import arm
from verify_binary_ternary_A2_original_family import greedy_ideal,UI
def at(p,n):return p[n] if 0<=n<len(p) else 0
def window(p,t):
    prefix=[0]
    for x in p:prefix.append(prefix[-1]+x)
    return [prefix[min(n+1,len(p))]-prefix[max(0,n+1-t)] for n in range(len(p)+t-1)]
def weighted_D_UI(p):
    falling=False;previous=0
    for n,x in enumerate(p):
        d=max(0,x-at(p,n-1));difference=2*d-previous
        if falling and difference>0:return False
        if difference<0:falling=True
        previous=d
    return True
def fast_greedy(host):
    """Unique leftmost embeddings; contiguous LETTER intervals from record host values.
    Direct state DP. It does not use the arm recurrence or core identity.
    """
    L=len(host);dp=[[] for _ in range(L+1)];dp[0]=[1]
    for state in range(L):
        src=dp[state]
        if not src:continue
        prefix=[0]
        for x in src:prefix.append(prefix[-1]+x)
        largest=0
        for j in range(state,L):
            hi=host[j]
            if hi<=largest:continue
            lo=largest+1;largest=hi;dst=dp[j+1];end=len(src)+hi
            if len(dst)<end:dst += [0]*(end-len(dst))
            for n in range(lo,end):
                dst[n]+=prefix[min(len(src),n-lo+1)]-prefix[max(0,n-hi)]
    result=[0]*(sum(host)+1)
    for p in dp:
        for n,x in enumerate(p):result[n]+=x
    return result
def fast_core(A,B,M):
    C=fastconv(A,B);S=[0]+window(C,M)
    L=[x-at(C,n)+at(A,n) for n,x in enumerate(S)]
    R=[x-at(C,n)+at(B,n) for n,x in enumerate(S)]
    H=[x+at(B,n) for n,x in enumerate(L)]
    assert min(L)>=0 and min(R)>=0
    return H,L,R
def first_missing(alpha,U):
    return min([len(U)+2]+[t+1+len(U)-i-1 for i,t in enumerate(U)])
def main():
    start=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=Random(2026110212)
    for _ in range(50):
        host=[rng.randint(1,5) for _ in range(rng.randint(1,7))]
        assert fast_greedy(host)==greedy_ideal(host)
        ct['fast_greedy_vs_original_independent_letter_DP_controls']+=1
    for K in [10,11,12]:
        opposites=[(1,[K-1]*(K-2)),(1,list(range(2,K))),
                   (5,[K-1]*(K+2)),(K+7,[2]*4+list(range(3,K)))]
        owners=[(1,[2]*6),(2,[2]*12),(1,[2,3,5,8]),(3,[3,4,7])]
        for alpha,U in owners:
          A=arm(alpha,U)[:-2]
          for beta,V in opposites:
            assert first_missing(beta,V)==K
            B=arm(beta,V)[:-2];p=fastconv(A[::-1],B[::-1]);D=len(p)-1
            assert weighted_D_UI(p);ct['actual_OLD_FULL_A2_pairs']+=1
            E=[2*x-at(p,n-1) for n,x in enumerate(p)]+[-p[-1],0]
            m=max(n for n,x in enumerate(p) if x==max(p))
            u=[max(0,x-at(p,n-1)) for n,x in enumerate(p)]
            f=[x<<n for n,x in enumerate(u)];ell=f.index(max(f))
            for n in range(m+1,len(p)):
                if E[n]<0:continue
                T=E[n+1]-E[n]
                for k in range(min(ell,max(0,D-n-2))):
                    if p[n]<=p[k] or at(p,n+1)<=p[k+1] or E[n]>E[k]:continue
                    assert T<=E[k+1]-E[k]
                    ct['ALL_proper_CLOSED_source_head_payments']+=1
                    if E[n]==E[k]:ct['EQUAL_proper_source_head_payments']+=1
            for t in [1,2,3,5,K-3,K,K+7,2*K+1]:
                P=window(p,t);assert weighted_D_UI(P)
                c=max(m,t-1)
                g=window(u,t) if m>=t-1 else p
                assert all(max(0,at(P,n)-at(P,n-1))==at(g,n) for n in range(c+1))
                assert max(0,at(P,c+1)-at(P,c))<=at(g,c+1)
                ct['ENTIRE_window_A2_and_head_boundary_checks']+=1
    for jumps in [5,6,7]:
      for base in [[3,4],[4,4,4]]:
        alpha,beta=1,2;U=list(base);V=[2]+list(base)
        for W in [U,V]:
            for _ in range(jumps):W.append(max(5,2*sum(t for t in W if t>=3)))
        assert first_missing(alpha,U)<=12 and first_missing(beta,V)<=12
        for extra in [False,True]:
            a,b=alpha,beta;X,Y=list(U),list(V)
            if extra:
                if a+sum(X)<b+sum(Y):a,b,X,Y=b,a,Y,X
                X.append(max(X)+1);ct['arbitrary_extra_heavier_append_originals']+=1
            M=max(X+Y)+1;A=arm(a,X)[:-2];B=arm(b,Y)[:-2]
            H,L,R=fast_core(A,B,M);host=[1]*a+X+[M]+list(reversed([1]*b+Y))
            actual=fast_greedy(host);assert actual==H and all(UI(p) for p in [actual,L,R])
            ct['TRUE_greedy_original_BOTH_five_to_seven_dominant_arms']+=1
            ct['TRUE_greedy_original_rank_counts']+=len(actual);ct['BOTH_relative_polynomials']+=2
            sha.update(repr((host,actual,L,R)).encode())
            print(json.dumps(dict(jumps=jumps,base=base,extra=extra,ranks=len(actual),seconds=time.monotonic()-start)),flush=True)
    out=dict(status='PASS_QA_FIRST_MISSING_TWELVE_CLOSED_SOURCE_WINDOWS_AND_A18_ORIGINAL',
      scope='QA ONLY. Actual recurrence and true greedy embeddings. Does not replace the independently reconstructed complete finite certificate or unbounded written assembly.',
      counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-start)
    (ROOT/'audit_first_missing_twelve_original.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)
if __name__=='__main__':main()
