"""Independent direct convolution rebuild of every low-kappa boundary jet."""
from pathlib import Path
from collections import Counter
import hashlib,json,time,struct

ROOT=Path(__file__).resolve().parent


def append_direct(p,t):
    q=[1]+[0]*(len(p)-1)
    for i,x in enumerate(p[:-1]):
        for j in range(1,min(t,len(p)-1-i)+1):
            q[i+j]+=x
    return tuple(q)


def derivative(p):
    return (0,0)+tuple(max(p[i]-p[i-1],0) for i in range(2,len(p)))


def first_weight(p):
    for i in range(2,8):
        value=2*p[i-1]-p[i]
        if value:return i,value
    return 8,None


def row_key(row):
    return tuple(row['old_prefix']),row['t'],row['kap'],row['delta'],row['n'],row['value'],row['budget']


def main():
    started=time.monotonic()
    N=13
    stack=[]
    seen=set()
    canonical=set()
    bad=[]
    counts=Counter()
    for alpha in range(1,N+1):
        p=tuple(1 if i<=alpha else 0 for i in range(N+1))
        seen.add((p,1))
        stack.append((p,1))
    while stack:
        p,last=stack.pop()
        kap,delta=first_weight(p)
        assert kap<=7
        canonical.add((p,last,kap))
        d=derivative(p)
        counts['independent_states']+=1
        for t in range(max(2,last),N+1):
            q=append_direct(p,t)
            counts['independent_appends']+=1
            kn=min(kap+1,t+1)
            dn=(2*q[kn-1]-q[kn])
            ranks=([kap+3] if t==kap-1 else [])
            if t==kap:
                ranks.append(kap+4)
                if delta==2:ranks.append(kap+5)
            for n in ranks:
                if kap<3 or n>N:continue
                counts['independent_boundary_states']+=1
                value=2*q[n-1]-q[n]-(2*q[n-2]-q[n-1])
                B=max(1,dn*(dn+1)//2-1)
                if value>=B:continue
                dq=derivative(q)
                old_drop=any(d[i]<d[i-1] for i in range(2,n))
                new_drop=any(dq[i]<dq[i-1] for i in range(2,n+1))
                assert old_drop or new_drop
                counts['independent_excluded_small_budgets']+=1
                bad.append(dict(old_prefix=p,t=t,kap=kap,delta=delta,n=n,value=value,budget=B))
            if kn<=7 and (q,t) not in seen:
                seen.add((q,t))
                stack.append((q,t))
    state_hash=hashlib.sha256(repr(sorted(canonical)).encode()).hexdigest()
    producer=json.loads((ROOT/'probe_low_kappa_triangular_boundaries.json').read_text())
    assert producer['complete']
    assert state_hash==producer['reachable_state_sha256']
    assert len(canonical)==producer['states']
    assert Counter(map(row_key,bad))==Counter(map(row_key,producer['rejected_boundary_profiles']))
    assert counts['independent_appends']==producer['counts']['legal_jet_appends']
    assert counts['independent_boundary_states']==producer['counts']['boundary_states']
    assert counts['independent_excluded_small_budgets']==53
    fmt=struct.Struct('<'+'H'*(N+1))
    with (ROOT/'low_kappa_boundary_states.bin').open('rb') as stream:
        for F,last,kap in sorted(canonical):
            assert stream.read(fmt.size+2)==fmt.pack(*F)+bytes((last,kap))
        assert stream.read(1)==b''
    out=dict(status='PASS_COMPLETE_INDEPENDENT_LOW_KAPPA_BOUNDARY_RECONSTRUCTION',
             N=N,counts=dict(counts),reachable_state_sha256=state_hash,exact_state_set_equality=True,
             scope='Independent direct convolution and DFS rebuild ALL states and 53 exclusions; source-jet coverage and conditional TC induction remain written proof obligations. No original UI completion.',
             seconds=time.monotonic()-started)
    (ROOT/'verify_low_kappa_triangular_boundaries.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
