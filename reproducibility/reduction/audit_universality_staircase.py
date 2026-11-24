"""Independent embedding tests of the exact increasing-host criterion."""
from pathlib import Path
import json,random,sys,time
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT))
from audit_large_peak_skeleton import arm

def words(n):
    if n==0:
        yield ()
    for first in range(1,n+1):
        for rest in words(n-first):yield (first,)+rest

def embeds(word,host):
    i=0
    for c in host:
        if i<len(word) and word[i]<=c:i+=1
    return i==len(word)

def main():
    start=time.monotonic();rng=random.Random(2026102100)
    cases=embedding_checks=mode_checks=0
    cache={n:list(words(n)) for n in range(1,9)}
    for case in range(1800):
        T=sorted(rng.choices(range(1,15),k=rng.randrange(1,18)))
        a=sum(T)
        ones=next((i for i,t in enumerate(T) if t>1),len(T))
        alpha=ones;U=T[ones:]
        if alpha==0:alpha=U.pop(0)
        q=arm(alpha,U)[::-1]
        for n in range(1,9):
            actual=all([embeds(w,T) for w in cache[n]])
            embedding_checks+=len(cache[n])
            criterion=len(T)>=n and all(t>=j for j,t in enumerate(T[-n:],1))
            assert actual==criterion
            if actual:
                s=len(U)
                assert s>=n-1
                assert 2*(a-s)>=2+n*(n-1)
                if n>=4:
                    last=max(i for i,c in enumerate(q) if c==max(q))
                    assert last>=n
                    mode_checks+=1
            cases+=1
        missing=next((n for n in range(1,len(T)+2)
                      if len(T)<n or any(t<j for j,t in enumerate(T[-n:],1))),None)
        assert missing is not None and 2*a>=missing*(missing-1)
    out=dict(status='PASS',scope='Finite independent embedding diagnostics of the written staircase theorem; no general core theorem inferred.',
             hosts=1800,host_weight_tests=cases,composition_embedding_tests=embedding_checks,
             universality_mode_checks=mode_checks,seed=2026102100,seconds=time.monotonic()-start)
    ROOT.joinpath('audit_universality_staircase.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)

if __name__=='__main__':main()
