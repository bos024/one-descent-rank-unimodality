"""Exact QA of the written SINGLE sorted-arm source-notch induction."""
from pathlib import Path
from collections import Counter
import struct,json,random,time
from probe_triangular_source_induction import data

ROOT=Path(__file__).resolve().parent


def inspect(F,k,last,counts):
    d=[0,0]+[max(0,F[i]-F[i-1]) for i in range(2,len(F))]
    ell=d.index(max(d));w=[0,0,0]+[3*F[i-1]-F[i]-2*F[i-2] for i in range(3,len(F))]
    for n in range(3,ell+1):
        counts['notch_edges']+=1
        if n!=last+2:assert w[n]>=w[n-1],(k,last,n,F)
        if w[n]<w[n-1]:counts['permitted_drops']+=1
    if last+3<=ell:
        assert w[last+3]>=w[last+1]
        counts['two_edge_recoveries']+=1
    record=0
    for n in range(ell+1):
        record=max(record,w[n])
        if n>=last+3:
            assert w[n]>=record
            counts['whole_earlier_record_comparisons']+=1
    counts['arms_or_exact_prefix_states']+=1


def main():
    started=time.monotonic();counts=Counter()
    raw=(ROOT/'low_kappa_joint_source_states.bin').read_bytes();fmt=struct.Struct('<'+'H'*48)
    for pos in range(0,len(raw),98):
        k=raw[pos+97]
        if k>=3:inspect(fmt.unpack_from(raw,pos),k,raw[pos+96],counts)
    counts['complete_N47_nonrect_prefix_states']=counts['arms_or_exact_prefix_states']
    rng=random.Random(2026102613)
    for case in range(18000):
        alpha=rng.randrange(1,130)
        if case%4==0:U=[2]*rng.randrange(2,45)+sorted(rng.choices(range(3,70),k=rng.randrange(0,6)))
        elif case%4==1:U=sorted(rng.choices(range(2,90),k=rng.randrange(2,40)))
        elif case%4==2:
            kk=rng.randrange(3,28);U=list(range(2,kk))+sorted(rng.choices(range(kk,100),k=rng.randrange(0,8)))
        else:
            T=rng.randrange(6,100);alpha=rng.randrange(T,T+120);U=[2,T,T+1]
        F,E,D,k,d,ell=data(alpha,U)
        inspect(F,k,U[-1],counts)
        if case%4==3:
            T=U[1]
            assert (k,d,E[k+1],ell,max(D))==(5,2,6,T+3,2*T-1)
            assert E[T+2]-E[T+1]==2*T-2
            assert E[T+3]-E[T+2]==2*T-3
            counts['unbounded_obstruction_family_instances']+=1
    out=dict(status='PASS_FINITE_QA_SINGLE_NOTCH_AND_SHARP_LATE_MONOTONICITY_OBSTRUCTION',counts=dict(counts),
             seconds=time.monotonic()-started,
             scope='Finite QA supports the separate unbounded written induction. Single-notch theorem is not inferred from nonfailure. Original UI/C/A2 OPEN.')
    (ROOT/'probe_source_single_notch.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
