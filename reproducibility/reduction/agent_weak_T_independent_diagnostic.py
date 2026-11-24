"""Independent direct actual-coefficient check of half-tail weaker curvature.

Constructs reverse arms directly by interval windows + terminal units. Does
not use any source-layer or induction identity from the written proof.
"""
from pathlib import Path
from collections import Counter
import sys,json,random,time,argparse
ROOT=Path(__file__).resolve().parent;sys.path.insert(0,str(ROOT))
from audit_joint_structure import fastconv

def reverse_arm(alpha,U):
    q=[1]*(alpha+1);weight=alpha
    for t in U:
        new=[0]*(weight+t+1);running=0
        for i in range(len(new)):
            if i<len(q):running+=q[i]
            if 0<=i-t<len(q):running-=q[i-t]
            new[i]=running
        weight+=t;new[weight]+=1;q=new
    return q

def parts(n,lo=2):
    if n==0:yield ()
    for t in range(lo,n+1):
        for rest in parts(n-t,t):yield (t,)+rest

def inspect(qX,qY,X,Y,counts):
    p=fastconv(qX,qY);D=len(p)-1;peak=max(p)
    ell=next(i for i in range(D,-1,-1) if p[i]==peak)
    counts['actual_pairs']+=1
    for n in range(ell+1,D//2+1):
        T=2*p[n+1]-3*p[n]+p[n-1];E=2*p[n]-p[n-1]
        counts['half_tail_comparisons']+=1
        counts['nonnegative_source_half_tail_comparisons']+=int(E>=0)
        if T>0:return dict(X=X,Y=Y,n=n,lastmode=ell,D=D,E=E,T=T,triple=p[n-1:n+2])
    return None

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--weight',type=int,default=17)
    parser.add_argument('--random',type=int,default=1200);args=parser.parse_args()
    start=time.monotonic();counts=Counter();failure=None;arms=[]
    for weight in range(1,args.weight+1):
        for alpha in range(1,weight+1):
            for U in parts(weight-alpha):arms.append((reverse_arm(alpha,U),(alpha,U)))
    counts['exhaustive_actual_arms_including_rectangles']=len(arms)
    for i,(qX,X) in enumerate(arms):
        for qY,Y in arms[i:]:
            failure=inspect(qX,qY,X,Y,counts)
            if failure:break
        if failure:break
        if i%200==199:print(json.dumps(dict(stage='exhaustive',done=i+1,counts=counts,seconds=time.monotonic()-start)),flush=True)
    rng=random.Random(2026102717)
    for rep in range(args.random if failure is None else 0):
        specs=[];polys=[]
        for side in range(2):
            h=rng.randrange(0,60);cap=rng.randrange(3,110)
            U=sorted(rng.choices(range(2,cap+1),k=h)) if rep%3 else [2]*h
            alpha=rng.randrange(1,550)
            specs.append((alpha,U));polys.append(reverse_arm(alpha,U))
        failure=inspect(*polys,*specs,counts)
        if failure:break
        if rep%200==199:print(json.dumps(dict(stage='random',done=rep+1,counts=counts,seconds=time.monotonic()-start)),flush=True)
    out=dict(status='STRONG_HALF_TAIL_CURVATURE_COUNTEREXAMPLE' if failure else 'PASS_FINITE_DIRECT_ACTUAL_HALF_TAIL_CURVATURE_DIAGNOSTIC',
             failure=failure,counts=counts,seconds=time.monotonic()-start,
             scope='Independent finite exact check only. Checks ALL T, without an E>=0 guard, after the actual LAST ordinary mode through degree midpoint; guarded weak-T is a subset. No unbounded conclusion inferred from these tests.')
    (ROOT/'agent_weak_T_independent_diagnostic.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)

if __name__=='__main__':main()
