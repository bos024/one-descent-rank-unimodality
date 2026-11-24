"""Test the full second source overlap on actual BOTH-rising derivative edges."""
from pathlib import Path
from collections import Counter
import json,random,time
from probe_double_defect_tail_recovery import prefix

ROOT=Path(__file__).resolve().parent


def main():
    rng=random.Random(2026102612);started=time.monotonic();counts=Counter()
    witness=None;tight=None;kappa_three_jets=set()
    def word(kind):
        k=rng.randrange(3,31)
        if kind==0:return list(range(2,k))
        if kind==1:return [k-1]*rng.randrange(k-2,k+25)
        if kind==2:return sorted(rng.choices(range(2,100),k=rng.randrange(2,45)))
        if kind==3:return list(range(2,k))+sorted(rng.choices(range(k,90),k=rng.randrange(0,7)))
        if kind==4:return [2]+sorted(rng.choices(range(3,150),k=rng.randrange(1,6)))
        if kind==5:return [2]*rng.randrange(3,50)
        return [k-1]*rng.randrange(k-2,k+6)+list(range(k,k+rng.randrange(1,16)))
    for case in range(120000):
        U=word(case%7);V=word((case//7)%7)
        alpha=rng.randrange(1,160);beta=rng.randrange(1,160)
        N=len(U)+len(V)+5
        A,p=prefix(alpha,U,N);B,q=prefix(beta,V,N);n=p+q+1
        A+= [0]*(N+1-len(A));B+= [0]*(N+1-len(B))
        counts['actual_pairs']+=1
        da=A[n]-A[n-1];dap=A[n-1]-A[n-2]
        db=B[n]-B[n-1];dbp=B[n-1]-B[n-2]
        if not (da>dap>0 and db>dbp>0):continue
        counts['both_primitives_strictly_rising']+=1
        dx=2*A[p-1]-A[p];ex=2*A[p]-A[p+1]
        dy=2*B[q-1]-B[q];ey=2*B[q]-B[q+1]
        if p==3:kappa_three_jets.add((dx,ex))
        if q==3:kappa_three_jets.add((dy,ey))
        sx=3*A[n-1]-A[n]-2*A[n-2];sy=3*B[n-1]-B[n]-2*B[n-2]
        margin=sx+sy-dx*ey-dy*ex
        if tight is None or margin<tight['margin']:
            tight=dict(alpha=alpha,U=U,beta=beta,V=V,p=p,q=q,dx=dx,ex=ex,dy=dy,ey=ey,
                       n=n,sx=sx,sy=sy,margin=margin)
        if margin<0:
            witness=tight;break
        if case%20000==19999:
            print(json.dumps(dict(done=case+1,counts=dict(counts),seconds=time.monotonic()-started)),flush=True)
    out=dict(status='ACTUAL_SECOND_OVERLAP_HALVING_COUNTEREXAMPLE' if witness else 'FINITE_FULL_SECOND_OVERLAP_NONFAILURE_ONLY',
             counts=dict(counts),witness=witness,tightest=tight,kappa_three_jets=sorted(kappa_three_jets),
             seconds=time.monotonic()-started,scope='Full second overlap halving diagnostics. General theorem, original UI and all later overlaps require proof; finite nonfailure is not a proof.')
    (ROOT/'probe_second_overlap_all_multiplicities.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
