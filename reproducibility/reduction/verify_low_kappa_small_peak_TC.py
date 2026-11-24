"""Independent rolling-window/DFS reconstruction of the complete N45 jet set."""
from pathlib import Path
from collections import Counter
import hashlib,json,struct,time

ROOT=Path(__file__).resolve().parent


def rolling_append(p,t):
    q=[1]
    s=0
    for n in range(1,len(p)):
        s+=p[n-1]
        if n>t:s-=p[n-t-1]
        q.append(s)
    return tuple(q)


def differences(p):
    return [0,0]+[max(p[i]-p[i-1],0) for i in range(2,len(p))]


def main():
    started=time.monotonic()
    N=45
    fmt=struct.Struct('<'+'H'*(N+1))
    stack=[]
    visited=set()
    counts=Counter()
    for alpha in range(1,N+1):
        p=tuple(int(i<=alpha) for i in range(N+1))
        key=fmt.pack(*p)+bytes([1,2])
        visited.add(key)
        stack.append(key)
    while stack:
        key=stack.pop()
        p=fmt.unpack_from(key)
        last,kap=key[-2:]
        d=differences(p)
        m=d.index(max(d))
        eligible=kap>=3 and m<=kap+2
        counts['independent_states']+=1
        for t in range(max(2,last),N+1):
            q=rolling_append(p,t)
            dq=differences(q)
            kn=min(kap+1,t+1)
            dn=2*q[kn-1]-q[kn]
            assert dn>0
            counts['independent_appends']+=1
            if eligible:
                counts['independent_eligible_appends']+=1
                B=max(1,dn*(dn+1)//2-1)
                for n in range(2,min(N,m+t)+1):
                    if dq[n]<dq[n-1]:break
                    if n<kn+3 or n<m+2 or d[n-1]<=0:continue
                    value=3*q[n-1]-q[n]-2*q[n-2]
                    counts['independent_necessary_guard_comparisons']+=1
                    assert value>=B,(p,t,kap,m,n,value,B)
            if kn<=7:
                if max(dq)>128:
                    counts['independent_slope_prunings']+=1
                    continue
                newkey=fmt.pack(*q)+bytes([t,kn])
                if newkey not in visited:
                    visited.add(newkey)
                    stack.append(newkey)
        if counts['independent_states']%100000==0:
            print(json.dumps(dict(states=counts['independent_states'],seen=len(visited),
                                  seconds=time.monotonic()-started)),flush=True)
    digest=hashlib.sha256(b''.join(sorted(visited))).hexdigest()
    producer=json.loads((ROOT/'probe_low_kappa_small_peak_TC.json').read_text())
    assert producer['complete'] and producer['remaining_queue']==0
    assert digest==producer['reachable_state_sha256']
    assert len(visited)==producer['states']
    mapping=dict(independent_states='expanded_states',independent_appends='legal_jet_appends',
                 independent_eligible_appends='eligible_early_old_peak_appends',
                 independent_necessary_guard_comparisons='necessary_guard_TC_comparisons',
                 independent_slope_prunings='monotone_slope_budget_prunings')
    for independent,original in mapping.items():
        assert counts[independent]==producer['counts'][original],(independent,original)
    with (ROOT/'low_kappa_small_peak_states.bin').open('rb') as stream:
        for key in sorted(visited):
            assert stream.read(fmt.size+2)==key
        assert stream.read(1)==b''
    out=dict(status='PASS_COMPLETE_INDEPENDENT_EARLY_PEAK_TC_JET_RECONSTRUCTION',
             N=N,slope_cap=128,counts=dict(counts),reachable_state_sha256=digest,exact_state_set_equality=True,
             scope='Independently rebuilds ALL N45 bounded-slope jets and necessary-guard comparisons. Unbounded rank reduction, actual coverage and TC induction must still be reviewed. No original UI completion.',
             seconds=time.monotonic()-started)
    (ROOT/'verify_low_kappa_small_peak_TC.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
