"""Independently reconstruct depth mixtures, their thresholds, and actual coefficient ranks."""
from itertools import combinations_with_replacement,accumulate
from random import Random
from collections import Counter
from pathlib import Path
from hashlib import sha256
import json
HERE=Path(__file__).resolve().parent
def fastconv(p,q):
    """Nonnegative integer convolution by carry-free byte packing."""
    bound=min(len(p),len(q))*max(p)*max(q)
    width=max(1,(bound.bit_length()+7)//8)
    a=int.from_bytes(b''.join(x.to_bytes(width,'little') for x in p),'little')
    b=int.from_bytes(b''.join(x.to_bytes(width,'little') for x in q),'little')
    buf=(a*b).to_bytes(width*(len(p)+len(q)-1),'little')
    return [int.from_bytes(buf[i:i+width],'little') for i in range(0,len(buf),width)]

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

def UI(p):
    k=p.index(max(p))
    return all(p[n]<=p[n+1] for n in range(k)) and all(p[n]>=p[n+1] for n in range(k,len(p)-1))

def greedy_ideal(host):
    """Each composition follows its UNIQUE greedy leftmost embedding.
    States retain its last matched host position. No arm/core recurrence used.
    """
    L=len(host);N=sum(host);dp=[[0]*(N+1) for _ in range(L+1)];dp[0][0]=1
    for state in range(L):
        first={}
        for j in range(state,L):
            for x in range(1,host[j]+1):
                if x not in first:first[x]=j+1
        for x,target in first.items():
            for n,v in enumerate(dp[state][:-x]):
                if v:dp[target][n+x]+=v
    return [sum(dp[state][n] for state in range(L+1)) for n in range(N+1)]

def at(row,k):return row[k] if 0<=k<len(row) else 0
def main():
    rng=Random(50134);counts=Counter();digest=sha256()
    def one(U,pads,literal):
        h=len(U);rows=[];P=[1]
        for b in reversed(U):
            rows.append(P);P=fastconv(P,[0]+[1]*b)
        n=sum(U)+max(pads)+3
        C=[0]*n;d=[0]*n;L=[0]*n
        for q,t in zip(rows,reversed(U)):
            W=list(accumulate(q+[0]*(n-len(q))))
            for k in range(n):
                C[k]+=W[k];d[k]+=W[k]-at(W,k-t+1);L[k]+=at(W,k-t+1)
        assert all(C[k]**2>=C[k-1]*C[k+1] for k in range(1,n-1))
        assert all(d[k]*C[k+1]>=d[k+1]*C[k] for k in range(n-1))
        counts['depth_capacity_minor_edges']+=n-1
        for alpha in pads:
            x=fast_greedy([1]*alpha+list(U));gg=list(accumulate(x+[0]*(n-len(x))))
            if literal:assert x==greedy_ideal([1]*alpha+list(U))
            dd=[max(0,at(x,k+2)-at(x,k+1)) for k in range(n)]
            assert all(dd[k]==max(0,d[k]-at(P,k-alpha+1)) for k in range(n))
            assert all(gg[k+1]*C[k]>=gg[k]*C[k+1] for k in range(n-1))
            assert all(dd[k+1]*C[k]<=dd[k]*C[k+1] for k in range(n-1))
            least=None
            for k in range(1,n):
                if least is None or gg[k]*gg[least-1]<gg[k-1]*gg[least]:least=k
                assert gg[least]*dd[k-1]>=gg[least-1]*dd[k]
                counts['all_delays_lower_envelope_checks']+=1
            assert all(gg[k]**2>=gg[k-1]*gg[k+1] for k in range(1,n-1))
            counts['actual_arms']+=1;counts['true_cumulative_LC_edges']+=n-2
            digest.update(repr((alpha,tuple(U),d,C,x)).encode())
    for h in range(1,7):
        for U in combinations_with_replacement(range(2,10),h):
            one(U,(1,2,7),h<=3 and max(U)<=6)
    for h in [11,27,45,86,133]:
        for c in [2,3,5,8,14]:
            U=sorted(rng.choices(range(2,c+1),k=h))
            one(U,(1,13,57),False)
    for case in range(160):
        def word():
            return sorted(rng.choices(range(2,rng.randint(5,32)),k=rng.randint(1,22)))
        X=word();Y=word();a=rng.randint(1,9);b=rng.randint(1,9);m=max(X+Y)+rng.randint(1,21)
        A=fast_greedy([1]*a+X);B=fast_greedy([1]*b+Y)
        H,L,R=fast_core(A,B,m)
        assert H==fast_greedy([1]*a+X+[m]+[1]*b+Y)
        assert H==fast_greedy([1]*a+X+[m]+Y[::-1]+[1]*b)
        assert all(UI(v) for v in (H,L,R)) and weighted_D_UI(fastconv(A,B)[::-1])
        counts['actual_strict_pairs']+=1;counts['actual_original_ranks']+=len(H)
        digest.update(repr((X,Y,m,H,L,R)).encode())
    result=dict(status='PASS_DEPTH_SLACK_TRUE_ARMS_AND_ORIGINAL_COEFFICIENTS',counts=dict(counts),digest=digest.hexdigest())
    print(result,flush=True);(HERE/'depth_slack_actual_audit.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
if __name__=='__main__':main()