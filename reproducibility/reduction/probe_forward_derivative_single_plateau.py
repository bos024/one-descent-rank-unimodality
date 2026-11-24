"""Test a proposed one-exception strict-rising rule for actual forward D."""
from pathlib import Path
import json,random,struct,time
from probe_triangular_source_induction import data

ROOT=Path(__file__).resolve().parent


def main():
    started=time.monotonic()
    counts=dict(complete_jet_profiles=0,wide_actual_profiles=0,interior_flat_edges=0)
    failures=[]
    fmt=struct.Struct('<'+'H'*46)
    with (ROOT/'low_kappa_small_peak_states.bin').open('rb') as stream:
        while row:=stream.read(fmt.size+2):
            F=fmt.unpack_from(row)
            last,kap=row[-2:]
            D=[0,0]+[max(F[i]-F[i-1],0) for i in range(2,46)]
            if max(D)==0:continue
            m=D.index(max(D))
            flat=[i for i in range(3,m+1) if D[i]==D[i-1]]
            if len(flat)>1 or (flat and flat[0]!=last+1):
                failures.append(dict(scope='ACTUAL_PREFIX_SIGNATURE',last=last,kap=kap,F=F,D=D,m=m,flat=flat))
                break
            assert max(D)>=m-2
            counts['interior_flat_edges']+=len(flat)
            counts['complete_jet_profiles']+=1
    rng=random.Random(2026102605)
    for _ in range(15000):
        alpha=rng.randrange(1,200)
        U=sorted(rng.choices(range(2,70),k=rng.randrange(1,30)))
        F,E,D,kap,delta,m=data(alpha,U)
        flat=[i for i in range(3,m+1) if D[i]==D[i-1]]
        if len(flat)>1 or (flat and flat[0]!=U[-1]+1):
            failures.append(dict(scope='FULL_ACTUAL_ARM',alpha=alpha,U=U,kap=kap,delta=delta,m=m,flat=flat))
            break
        assert max(D)>=m-2
        counts['wide_actual_profiles']+=1
        counts['interior_flat_edges']+=len(flat)
    out=dict(status='ACTUAL_STRICT_RISING_RULE_COUNTEREXAMPLE' if failures else 'FINITE_QA_ONLY_STRICT_RISING_RULE',
             counts=counts,failures=failures,seconds=time.monotonic()-started,
             scope='Tests proposed strict growth of D before FIRST global mode except possibly at lastcap+1. Unbounded proof must be checked separately. Original UI OPEN.')
    (ROOT/'probe_forward_derivative_single_plateau.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
