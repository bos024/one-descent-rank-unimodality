"""Falsify a proposed sharper source localization before using it.

Hypothesis: a nonnegative forward twice-coefficient deficit cannot
decrease once the shared rank is beyond BOTH arms' first defects.
Only exact actual low coefficients are used. This is not a theorem.
"""
from pathlib import Path
from collections import Counter
import random,time,json
from audit_joint_structure import fastconv

ROOT=Path(__file__).resolve().parent


def prefix(alpha,U,limit):
    # The initial all-ones arm already misses (2), irrespective of alpha.
    A=[1]*min(alpha+1,limit+1);kappa=2
    for t in U:
        n=min(len(A)+t,limit+1);B=[1]+[0]*(n-1);running=0
        for j in range(1,n):
            if j-1<len(A):running+=A[j-1]
            if 0<=j-1-t<len(A):running-=A[j-1-t]
            B[j]=running
        A=B;kappa=min(t+1,kappa+1)
    return A,kappa


def main():
    start=time.monotonic();rng=random.Random(2026103015);counts=Counter();witness=None;maximum=None
    for rep in range(75000):
        h=rng.randrange(2,65);g=rng.randrange(2,65);limit=2*(h+g)+5
        if rep%4==0:
            U=[rng.randrange(2,95)]*h;V=[rng.randrange(2,95)]*g
        elif rep%4==1:
            U=sorted(rng.choices(range(2,9),k=h));V=sorted(rng.choices(range(2,95),k=g))
        else:
            U=sorted(rng.choices(range(2,95),k=h));V=sorted(rng.choices(range(2,95),k=g))
        alpha=rng.randrange(1,200);beta=rng.randrange(1,200)
        A,ka=prefix(alpha,U,limit);B,kb=prefix(beta,V,limit);P=fastconv(A,B)
        counts['actual_pairs']+=1
        for j in range(1,min(limit,len(P)-1)):
            current=2*P[j]-P[j+1];recovery=P[j+1]-3*P[j]+2*P[j-1]
            if current<0 or recovery<=0:continue
            counts['nonnegative_positive_tail_recovery_ranks']+=1
            row=dict(alpha=alpha,U=U,beta=beta,V=V,j=j,kappaA=ka,kappaB=kb,current_e=current,tail_increment=recovery,
                P_prev=P[j-1],P_now=P[j],P_next=P[j+1])
            if maximum is None or j-max(ka,kb)>maximum[0]:maximum=(j-max(ka,kb),row)
            if j>max(ka,kb):
                witness=row;break
        if witness:break
        if rep%5000==0:print(json.dumps(dict(progress=rep,counts=dict(counts),largest_offset=None if maximum is None else maximum[0])),flush=True)
    out=dict(status='EXACT_DOUBLE_DEFECT_LOCALIZATION_COUNTEREXAMPLE' if witness else 'FINITE_DOUBLE_DEFECT_LOCALIZATION_NONFAILURE_ONLY',
        counts=dict(counts),witness=witness,largest_offset_example=None if maximum is None else maximum[1],seconds=time.monotonic()-start,
        scope='The extra localization is only a proposed shortcut; a witness does NOT refute C,S,A2 or the original conjecture. A finite pass is NOT a proof.')
    (ROOT/'probe_double_defect_tail_recovery.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)


if __name__=='__main__':main()
