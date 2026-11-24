"""Bounded-rank source jets for low-first-weight TC cases at ALL old peaks.

An unfinished run is explicitly partial.  This is a stronger finite necessary-
guard diagnostic, not a proof of original unimodality or global TC.
"""
from pathlib import Path
from collections import Counter,deque
import argparse,json,struct,time,pickle,hashlib
from probe_low_kappa_triangular_boundaries import app,slopes,source,nondecreasing

ROOT=Path(__file__).resolve().parent


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--N',type=int,default=39)
    ap.add_argument('--limit',type=int,default=300000)
    ap.add_argument('--seconds',type=int,default=39)
    ap.add_argument('--resume',action='store_true')
    args=ap.parse_args()
    N=args.N
    started=time.monotonic()
    queue=deque()
    seen=set()
    counts=Counter()
    unresolved=[]
    pack=struct.Struct('<'+'H'*(N+1)).pack
    checkpoint=ROOT/'low_kappa_strict_peak_TC_checkpoint.pickle'
    previous_seconds=0
    if args.resume:
        with checkpoint.open('rb') as stream:
            saved=pickle.load(stream)
        assert saved['N']==N
        queue,seen,counts,unresolved=(saved[k] for k in ['queue','seen','counts','unresolved'])
        previous_seconds=saved['seconds']
    else:
        for alpha in range(1,N+1):
            F=tuple(int(i<=alpha) for i in range(N+1))
            key=pack(*F)+bytes((1,2))
            seen.add(key)
            queue.append(key)
    complete=True
    while queue:
        if len(seen)>args.limit or time.monotonic()-started>args.seconds:
            complete=False
            break
        key=queue.popleft()
        F=struct.unpack_from('<'+'H'*(N+1),key)
        last,kap=key[-2:]
        delta=2*F[kap-1]-F[kap]
        counts['expanded_states']+=1
        D=slopes(F)
        m=D.index(max(D))
        eligible=kap>=3
        for t in range(max(2,last),N+1):
            kn=min(kap+1,t+1)
            if kn>8:continue
            dn=1 if t==kap-1 else delta+1 if t==kap else delta
            Fn=app(F,t)
            counts['legal_jet_appends']+=1
            Dn=slopes(Fn)
            if eligible:
                En=source(Fn)
                B=max(1,dn*(dn+1)//2-1)
                counts['eligible_all_old_peak_appends']+=1
                last_monotone=1
                for i in range(2,N+1):
                    if Dn[i]<Dn[i-1]:break
                    last_monotone=i
                for n in range(max(kn+3,m+2),min(N,m+t,last_monotone)+1):
                    if D[n-1]<=0:continue
                    value=En[n]-En[n-1]
                    counts['necessary_guard_TC_comparisons']+=1
                    if value<B:
                        counts['unresolved_small_curvatures']+=1
                        if len(unresolved)<12:
                            unresolved.append(dict(old_prefix=F,t=t,kap=kap,delta=delta,
                                old_mode=m,old_M=max(D),n=n,value=value,budget=B,D=D,Dn=Dn))
            if kn<=7:
                if max(Dn)>35:
                    counts['monotone_slope_budget_prunings']+=1
                    continue
                key=pack(*Fn)+bytes((t,kn))
                if key not in seen:
                    seen.add(key)
                    queue.append(key)
        if counts['expanded_states']%100000==0:
            print(json.dumps(dict(expanded=counts['expanded_states'],seen=len(seen),queue=len(queue),
                                  unresolved=counts['unresolved_small_curvatures'],
                                  seconds=previous_seconds+time.monotonic()-started)),flush=True)
    elapsed=previous_seconds+time.monotonic()-started
    with checkpoint.open('wb') as stream:
        pickle.dump(dict(N=N,queue=queue,seen=seen,counts=counts,
                         unresolved=unresolved,seconds=elapsed,complete=complete),stream,protocol=5)
    if complete:
        with (ROOT/'low_kappa_strict_peak_states.bin').open('wb') as stream:
            for state in sorted(seen):stream.write(state)
    out=dict(status='COMPLETE_ALL_PEAK_STRICTNESS_FINITE_JET_CALCULATION' if complete else 'PARTIAL_ALL_PEAK_STRICTNESS_FINITE_JET_DIAGNOSTIC',
             complete=complete,N=N,old_kappa_max=7,slope_cap=35,
             counts=dict(counts),states=len(seen),remaining_queue=len(queue),
             reachable_state_sha256=hashlib.sha256(b''.join(sorted(seen))).hexdigest(),
             unresolved_examples=unresolved,seconds=elapsed,
             scope='Finite stronger necessary-prefix-guard calculation. Needs separate rank-bound, coverage and mode audit before any TC theorem. General original UI remains OPEN.')
    (ROOT/'probe_low_kappa_strict_peak_TC.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='unresolved_examples'}),flush=True)


if __name__=='__main__':main()
