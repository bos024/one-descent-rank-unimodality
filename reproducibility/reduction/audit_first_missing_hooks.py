"""Independent word enumeration at the first missing level and sharp boundary height."""
from pathlib import Path
import json,random,sys,time
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT))
from audit_universality_staircase import words,embeds
from audit_large_peak_skeleton import arm,kernel,fastconv,at,window,add
from audit_unbounded_arm_bulk_source import renewal

def normalize(host):
    a=next((i for i,t in enumerate(host) if t>1),len(host))
    U=host[a:]
    if not a:a=U.pop(0)
    return a,U

def main():
    start=time.monotonic();rng=random.Random(2026102112)
    levels=word_checks=missing_checks=boundary_checks=0
    for case in range(1100):
        X=sorted(rng.choices(range(1,10),k=rng.randrange(1,10)))
        t=max(X)
        for cap in [t,None]:
            for n in range(1,len(X)+2):
                allowed=[w for w in words(n) if cap is None or max(w)<=cap]
                missed=[w for w in allowed if not embeds(w,X)]
                word_checks+=len(allowed)
                if not missed:continue
                hooks={(j,)+(1,)*(n-j) for j in range(1,(min(n,t) if cap else n)+1)}
                assert set(missed)<=hooks
                assert len(missed)<= (min(n-1,t) if cap else n)
                if cap is not None and t>=2:
                    alpha,U=normalize(X)
                    R=kernel(arm(alpha,U),t)
                    eps=int(not embeds((1,)*n,X))
                    assert R[n+1]>=2*len(missed)-eps
                missing_checks+=len(missed);levels+=1
                break
    for t in range(1,10):
        X=list(range(1,t+1));alpha,U=normalize(X)
        A=arm(alpha,U);M=t+1
        R=kernel(A,t)
        rho=next(i for i,c in enumerate(R) if c)
        assert rho==t+1 and R[rho]==t
        N=2*t+4
        AI=renewal(t,N);PI=fastconv(AI,AI)
        HI=add(AI,AI,[0]+window(PI,M),[-x for x in PI])[:N+1]
        H=add(fastconv(A,kernel(A,M)),A)
        mu=2*t+2
        assert all(HI[n]==at(H,n) for n in range(mu))
        assert HI[mu]-at(H,mu)==t*t+2*t
        boundary_checks+=1
    out=dict(status='PASS',scope='Independent bounded and unbounded word enumeration of the first-defect hook theorem, and exact sharp first-boundary amplitudes. No later-boundary sign claim.',
             seed=2026102112,first_missing_levels=levels,allowed_word_embedding_checks=word_checks,
             missing_words_verified_as_hooks=missing_checks,
             sharp_boundary_amplitude_examples=boundary_checks,seconds=time.monotonic()-start)
    ROOT.joinpath('audit_first_missing_hooks.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)

if __name__=='__main__':main()
