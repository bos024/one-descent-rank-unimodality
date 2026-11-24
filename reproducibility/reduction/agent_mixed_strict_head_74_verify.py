"""Exact QA of the strict opposite-head construction, not an unbounded proof.
Checks actual reverse appends and the independently retained main CI box.
"""
from pathlib import Path
from collections import Counter
import random,json,time,hashlib

ROOT=Path(__file__).resolve().parent


def interval(A,t,N):
    C=[0]*(N+1);run=0
    for n in range(N+1):
        if n<len(A):run+=A[n]
        if 0<=n-t<len(A):run-=A[n-t]
        C[n]=run
    return C


def check(K,beta,V,counts):
    N=(37*K-111)//2;wt=beta;kappa=2
    q=[1]*min(beta+1,N+1)+[0]*max(0,N-beta)
    box=q[:]
    for t in V:
        q=interval(q,t,N);box=interval(box,t,N);wt+=t
        if wt<=N:q[wt]+=1
        kappa=min(kappa+1,t+1)
    assert kappa==K
    M=beta+sum(t-1 for t in V);B=max([beta]+[t-1 for t in V])
    Mmin=1+(K-2)*(K-1)//2;other=1+(K-3)*(K-2)//2
    assert M>=Mmin and M-B>=other
    assert 2*N<=Mmin and N<=other
    assert N<=min(M//2,M-B)
    for n in range(N+1):
        dq=q[n]-(q[n-1] if n else 0)
        db=box[n]-(box[n-1] if n else 0)
        assert dq>=db>=1
        counts['actual_strict_head_coefficients']+=1
        counts['main_box_differences_dominated']+=1
    counts['actual_opposite_profiles']+=1
    return dict(K=K,beta=beta,g=len(V),N=N,M=M,other_degree=M-B,
                sha256=hashlib.sha256(repr((q,box)).encode()).hexdigest())


def main():
    start=time.monotonic();rng=random.Random(2026102674);counts=Counter();rows=[]
    for K in (74,75,96,239):
        N=(37*K-111)//2
        variants=[(1,list(range(2,K))),
                  (2*N+10,list(range(2,K))),
                  (1,list(range(2,K-1))+[2*N+13]),
                  (rng.randrange(1,30),[2]*(K+5)+list(range(3,K))),
                  (rng.randrange(1,30),sorted(rng.randrange(t,K) for t in range(2,K)))]
        for beta,V in variants:rows.append(check(K,beta,V,counts))
    for K in range(74,2001):
        N=(37*K-111)//2
        assert 2*N<=1+(K-2)*(K-1)//2
        assert N<=1+(K-3)*(K-2)//2
        counts['integer_budget_crosschecks']+=1
    K=73;N=(37*K-111)//2
    assert 2*N>1+(K-2)*(K-1)//2
    out=dict(status='PASS_EXACT_ACTUAL_STRICT_HEAD_AND_MAIN_BOX_DIFFERENCE_QA',
             counts=dict(counts),profiles=rows,seconds=round(time.monotonic()-start,3),
             independent_mathematical_review='Root and audit_linear_clipping agent independently checked raw-source single-term payment, main-box strictness, extra CI lower centers and sharper positive-recovery head bound.',
             scope='Finite diagnostics only. Unbounded 74 conclusion uses the written source-birth/CI proof and generic Lean kernels. The failure at73 is only of the sufficient budget, not an actual S counterexample. General original UI remains open.')
    (ROOT/'agent_mixed_strict_head_74_verify.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='profiles'}),flush=True)


if __name__=='__main__':main()
