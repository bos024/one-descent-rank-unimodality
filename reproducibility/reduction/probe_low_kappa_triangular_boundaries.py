"""Finite source-jet grammar for the low-kappa pre-old-peak TC boundaries.

A completed grammar is a finite coefficient calculation; its coverage and
the TC induction must be audited separately. Partial runs are never proofs.
"""
from pathlib import Path
from collections import Counter,deque
import argparse
import hashlib
import json
import time
import struct

ROOT=Path(__file__).resolve().parent


def app(F,t):
    C=[0]
    for x in F:C.append(C[-1]+x)
    return tuple([1]+[C[n]-C[max(0,n-t)] for n in range(1,len(F))])


def slopes(F):return [0,0]+[max(F[n]-F[n-1],0) for n in range(2,len(F))]


def source(F):return [0,0]+[2*F[n-1]-F[n] for n in range(2,len(F))]


def nondecreasing(v,n):return all(v[i]>=v[i-1] for i in range(1,n+1))


def excluded_mode(v,n):
    m=v.index(max(v))
    return m<n and any(v[i]<max(v[:i]) for i in range(m+1,len(v)))


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--limit',type=int,default=300000)
    ap.add_argument('--seconds',type=int,default=45)
    args=ap.parse_args()
    N=13
    started=time.monotonic()
    queue=deque()
    seen=set()
    counts=Counter()
    unresolved=[]
    rejected=[]
    for alpha in range(1,N+1):
        F=tuple(int(i<=alpha) for i in range(N+1))
        key=(F,1,2)
        seen.add(key)
        queue.append((F,1,2,2 if alpha==1 else 1,alpha,()))
    complete=True
    digest=hashlib.sha256()
    while queue:
        if len(seen)>args.limit or time.monotonic()-started>args.seconds:
            complete=False
            break
        F,last,kap,delta,alpha,U=queue.popleft()
        counts['expanded_states']+=1
        D=slopes(F)
        for t in range(max(2,last),N+1):
            kn=min(kap+1,t+1)
            if kn>8:continue
            dn=1 if t==kap-1 else delta+1 if t==kap else delta
            Fn=app(F,t)
            counts['legal_jet_appends']+=1
            Dn=slopes(Fn)
            En=source(Fn)
            ranks=[]
            if t==kap-1:ranks.append(kap+3)
            if t==kap:
                ranks.append(kap+4)
                if delta==2:ranks.append(kap+5)
            for n in ranks:
                if n>N or kap<3:continue
                counts['boundary_states']+=1
                value=En[n]-En[n-1]
                B=max(1,dn*(dn+1)//2-1)
                if value>=B:continue
                counts['raw_small_budget_boundaries']+=1
                rejected.append(dict(old_prefix=F,t=t,kap=kap,delta=delta,n=n,value=value,budget=B))
                if not nondecreasing(D,n-1) or not nondecreasing(Dn,n):
                    counts['excluded_by_earlier_strict_fall']+=1
                    continue
                if excluded_mode(D,n-1) or excluded_mode(Dn,n):
                    counts['excluded_by_certified_prefix_global_mode']+=1
                    continue
                counts['unresolved_necessary_prefix_guards']+=1
                digest.update(str((F,last,kap,delta,t,n,value,B)).encode())
                if len(unresolved)<16:
                    unresolved.append(dict(alpha=alpha,U=U,t=t,kap=kap,delta=delta,n=n,
                                           value=value,budget=B,D=D,Dn=Dn))
            if kn<=7:
                key=(Fn,t,kn)
                if key not in seen:
                    seen.add(key)
                    queue.append((Fn,t,kn,dn,alpha,U+(t,)))
        if counts['expanded_states']%10000==0:
            print(json.dumps(dict(expanded=counts['expanded_states'],seen=len(seen),
                                  queue=len(queue),unresolved=counts['unresolved_necessary_prefix_guards'],
                                  seconds=time.monotonic()-started)),flush=True)
    out=dict(status='COMPLETE_FINITE_JET_CALCULATION' if complete else 'PARTIAL_FINITE_JET_DIAGNOSTIC',
             complete=complete,N=N,old_kappa_max=7,counts=dict(counts),states=len(seen),
             remaining_queue=len(queue),unresolved_examples=unresolved,
             rejected_boundary_profiles=rejected,
             reachable_state_sha256=hashlib.sha256(repr(sorted(seen)).encode()).hexdigest(),
             unresolved_sha256=digest.hexdigest(),
             scope='Finite coefficient grammar only; actual coverage/mode certificates and full TC induction require separate proof. General S/A2/C/original UI remain OPEN.',
             seconds=time.monotonic()-started)
    if complete:
        pack=struct.Struct('<'+'H'*(N+1)).pack
        with (ROOT/'low_kappa_boundary_states.bin').open('wb') as stream:
            for F,last,kap in sorted(seen):
                stream.write(pack(*F)+bytes((last,kap)))
    (ROOT/'probe_low_kappa_triangular_boundaries.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['unresolved_examples','rejected_boundary_profiles']}),flush=True)


if __name__=='__main__':main()
