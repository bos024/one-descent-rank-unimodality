"""Search the remaining short-skeleton region after both mode-sensitive tests."""
from pathlib import Path
import sys,random,json,time

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'foundations'))
from audit_short_arm import forward,kernel,at,unimodal,window
from audit_cubic import conv


def lastmode(p):
    peak=max(p)
    return max(i for i,x in enumerate(p) if x==peak)


def min_layer_sum(p):
    right=len(p)-1;answer=2*right;firstmode=p.index(max(p))
    for left in range(firstmode+1):
        value=p[left]
        if value==0 or (left and value==p[left-1]):continue
        while p[right]<value:right-=1
        answer=min(answer,left+right)
    return answer


def normalize(alpha,U):
    U=list(U)
    if not U:return alpha,U
    if alpha==0:alpha=U.pop(0)
    if U and alpha<U[0]-1:alpha,U[0]=U[0]-1,alpha+1
    return alpha,U


def arm(alpha,U):
    p=[1]*(alpha+1)
    for t in U:p=[1]+window(p,t)
    return p


def main():
    rng=random.Random(2026101689);start=time.monotonic()
    kept=covered=extra_covered=0;failure=None;example=None;max_gap=0
    for c in range(30000):
        m=rng.randrange(8,250);t=rng.randrange(5,m)
        U=[t]
        V=sorted(rng.choices(range(2,m),k=rng.randrange(2,7)))
        u,v=t,sum(V)
        d=rng.randrange(4,min(2*m-3,2*u-1))
        alpha=t-1+rng.randrange(2*m)
        beta=m+alpha+u-d-v
        if beta<0:continue
        X=[1]*alpha+U;Y=[1]*beta+V;a,b=sum(X),sum(Y)
        A,B=arm(alpha,U),arm(beta,V);DX,DY=kernel(A,m),kernel(B,m)
        mx,my=lastmode(DX[::-1]),lastmode(DY[::-1]);N=a+b+m
        jy=2 if b>=2*m-1 and len(V)>=2 else int(b>=m)
        jx=int(a>=m)
        gap_x=u+b+m-1-((N+2+jy)//2+my)
        gap_y=v+a+m-1-((N+2+jx)//2+mx)
        if min(gap_x,gap_y)<=0:
            covered+=1;continue
        na,nU=normalize(alpha,U);nb,nV=normalize(beta,V)
        assert arm(na,nU)==A and arm(nb,nV)==B
        if not nU or not nV:
            extra_covered+=1;continue
        exact_gx=(a+min_layer_sum(DY)+1)//2
        exact_gy=(b+min_layer_sum(DX)+1)//2
        gap_x=sum(nU)+b+m-1-(exact_gx+my)
        gap_y=sum(nV)+a+m-1-(exact_gy+mx)
        if min(gap_x,gap_y)<=0:
            extra_covered+=1;continue
        kept+=1
        Q=conv(A,DY);H=[x+at(B,i) for i,x in enumerate(Q)]
        witness=dict(M=m,alpha=alpha,U=U,beta=beta,V=V,
                     weight=N,mode_gaps=[gap_x,gap_y])
        if min(gap_x,gap_y)>max_gap:
            max_gap=min(gap_x,gap_y);example=witness
        if not unimodal(H):failure=witness;break
        if c%3000==2999:
            print(json.dumps(dict(attempts=c+1,kept=kept,covered=covered,
                                 max_mode_gap=max_gap,seconds=time.monotonic()-start)),flush=True)
    result=dict(status='COUNTEREXAMPLE' if failure else 'NO COUNTEREXAMPLE FOUND',
                scope='finite diagnostic in cases not certified by either actual-mode criterion',
                attempts=c+1,kept=kept,covered_by_mode_criteria=covered,
                extra_covered_by_normalization_or_exact_layers=extra_covered,
                maximum_remaining_mode_gap=max_gap,example=example,failure=failure,
                seed=2026101689,seconds=time.monotonic()-start)
    ROOT.joinpath('probe_uncovered_short_skeleton.json').write_text(json.dumps(result,indent=2),encoding='utf8')
    print(json.dumps(result),flush=True)


if __name__=='__main__':main()
