"""Actual exact diagnostics for a triangular source-curvature induction.

The input is the true sorted append recurrence.  This is research evidence,
not a proof of the triangular curvature target or general S.
"""
from pathlib import Path
from collections import Counter
import json
import random
import time

from audit_large_peak_skeleton import arm, at

ROOT=Path(__file__).resolve().parent


def data(alpha,U):
    F=arm(alpha,U)
    h=len(U)
    kap=min([h+2]+[t+h-i for i,t in enumerate(U)]) if h else 2
    E=[int(n==0)-int(n==1)+2*at(F,n-1)-at(F,n) for n in range(len(F)+1)]
    assert all(v>=0 for v in E)
    delta=E[kap]
    D=[max(F[n]-at(F,n-1),0) if n>=2 else 0 for n in range(len(F))]
    ell=D.index(max(D)) if max(D)>0 else 0
    return F,E,D,kap,delta,ell


def budget(d):return max(1,d*(d+1)//2-1)


def main():
    started=time.monotonic()
    rng=random.Random(2026102604)
    counts=Counter()
    failures={}
    residual={}
    low_states=Counter()
    for case in range(50000):
        alpha=rng.randrange(1,70)
        if case%3==0:
            cap=rng.randrange(2,14)
            U=sorted(rng.choices(range(2,cap+1),k=rng.randrange(1,32)))
        elif case%3==1:
            kap0=rng.randrange(3,13)
            U=list(range(2,kap0))
            U=sorted([2]*rng.randrange(0,22)+U)
        else:
            U=sorted(rng.choices(range(2,28),k=rng.randrange(1,18)))
        _,E,D,kap,delta,ell=data(alpha,U)
        t=rng.choice([U[-1],max(U[-1],kap-1),max(U[-1],kap),
                      max(U[-1],kap+1),U[-1]+rng.randrange(1,28)])
        _,En,Dn,kn,dn,ln=data(alpha,U+[t])
        counts['actual_append_contexts']+=1
        for n in range(kn+3,ln+1):
            value=at(En,n)-at(En,n-1)
            counts['triangular_curvature_comparisons']+=1
            if value<budget(dn):
                failures.setdefault('target',dict(alpha=alpha,U=U,t=t,kap=kap,delta=delta,ell=ell,
                                                  kn=kn,dn=dn,ln=ln,n=n,value=value,budget=budget(dn)))
            if n-1>ell:
                counts['old_peak_crossings']+=1
                M=max(D)
                if M-1<budget(dn):
                    counts['peak_crossings_not_paid_by_M_minus_one']+=1
                    key=(kap,delta,kn,dn)
                    low_states[key]+=1
                    residual.setdefault(str(key),dict(alpha=alpha,U=U,t=t,ell=ell,M=M,
                        ln=ln,n=n,value=value,budget=budget(dn)))
            else:
                counts['pre_old_peak_comparisons']+=1
                if kap>=8:
                    counts['large_kappa_pre_peak']+=1
                    if kn==kap and n==kap+3:
                        counts['stationary_boundary_paid']+=1
                        assert value==at(E,kap+2)-at(E,3)
                    if kn==kap+1 and dn==delta+1 and n==kap+4:
                        counts['collision_first_boundary_paid']+=1
                        assert value==at(E,kap+3)-at(E,3)
                    if kn==kap+1 and dn==delta+1 and delta==2 and n==kap+5:
                        counts['collision_second_boundary_paid']+=1
                        assert value==at(E,kap+4)-at(E,4)
        # The large-kappa boundary profiles used in the proposed induction.
        if kap>=8:
            A3=at(E,kap+3)
            assert A3>=delta*(delta+3)//2
            counts['large_kappa_collision_profile_checks']+=1
    out=dict(status='EXACT_ACTUAL_TRIANGULAR_SOURCE_INDUCTION_DIAGNOSTIC',counts=dict(counts),
             failures=failures,small_peak_budget_states={str(k):v for k,v in sorted(low_states.items())},
             small_peak_budget_examples=residual,
             scope='Actual finite diagnostics only; triangular curvature, general S/C/A2 and original UI remain OPEN.',
             seconds=time.monotonic()-started)
    (ROOT/'probe_triangular_source_induction.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='small_peak_budget_examples'}),flush=True)


if __name__=='__main__':main()
