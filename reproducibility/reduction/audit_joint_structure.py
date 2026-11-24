"""Exact checks of proved forward/reverse difference shape and failed stronger LC claims."""
from pathlib import Path
import sys,random,json,time

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT))
from probe_uncovered_short_skeleton import arm
sys.path.insert(0,str(ROOT.parent/'foundations'))
from audit_short_arm import at,window,unimodal,kernel


def fastconv(p,q):
    """Nonnegative integer convolution by carry-free byte packing."""
    bound=min(len(p),len(q))*max(p)*max(q)
    width=max(1,(bound.bit_length()+7)//8)
    a=int.from_bytes(b''.join(x.to_bytes(width,'little') for x in p),'little')
    b=int.from_bytes(b''.join(x.to_bytes(width,'little') for x in q),'little')
    buf=(a*b).to_bytes(width*(len(p)+len(q)-1),'little')
    return [int.from_bytes(buf[i:i+width],'little') for i in range(0,len(buf),width)]


def main():
    rng=random.Random(2026101696);start=time.monotonic();comparisons=prefixes=0
    for case in range(8000):
        m=rng.randrange(3,55)
        U=sorted(rng.choices(range(2,m),k=rng.randrange(0,21)))
        V=sorted(rng.choices(range(2,m),k=rng.randrange(0,21)))
        alpha=rng.randrange(3*m);beta=rng.randrange(3*m)
        A=arm(alpha,U);B=arm(beta,V);a=len(A)-1;b=len(B)-1
        p=fastconv(A[::-1],B[::-1]);mode=p.index(max(p))
        assert unimodal(p)
        d=[max(0,at(p,i)-at(p,i-1)) for i in range(len(p))]
        assert unimodal(d)
        for i in range(1,mode+1):
            assert p[i]**2>=at(p,i-1)*at(p,i+1);comparisons+=1
        if max(A)>1 and max(B)>1:
            assert mode<max(a,b);prefixes+=1
        rng.shuffle(U)
        P=arm(alpha,U);first=P.index(max(P))
        dp=[max(0,at(P,i)-at(P,i-1)) for i in range(1,len(P))]
        assert unimodal(dp)
        if max(P)>1:assert all(P[i]>P[i-1] for i in range(2,first+1))
        rng.shuffle(V)
        formal=fastconv(P[::-1],arm(beta,V)[::-1]);fm=formal.index(max(formal))
        assert unimodal(formal)
        assert unimodal([max(0,at(formal,i)-at(formal,i-1)) for i in range(len(formal))])
        assert all(formal[i]**2>=at(formal,i-1)*at(formal,i+1) for i in range(1,fm+1))
    p=fastconv(arm(58,[2]*3)[::-1],arm(37,[2]*13)[::-1]);mode=p.index(max(p))
    assert mode==60
    d=[at(p,i)-at(p,i-1) for i in range(mode+1)];W=window(d,3)
    assert W[55:58]==[3194,1974,1220]
    assert W[56]**2-W[55]*W[57]==-4
    A=arm(1,[2,2,2]);assert A[2:5]==[2,3,5]
    formal_bad=kernel(arm(0,[4,4,4,4,2,2]),5)
    assert formal_bad[4:8]==[2,3,2,3] and not unimodal(formal_bad)
    out=dict(status='PASS',scope='diagnostics for analytic difference-shape propositions and two exact failed LC strengthenings',
             arm_pairs=case+1,formal_forward_arms=case+1,formal_products=case+1,
             rising_lc_comparisons=comparisons,nonrectangular_prefix_splices=prefixes,
             smoothing_counterexample=dict(M=3,alpha=58,U=[2]*3,beta=37,V=[2]*13,
                 index=56,values=W[55:58],determinant=-4),
             seed=2026101696,seconds=time.monotonic()-start)
    ROOT.joinpath('audit_joint_structure.json').write_text(json.dumps(out,indent=2),encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
