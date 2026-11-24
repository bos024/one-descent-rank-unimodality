"""Complete fixed-capacity C entrance, ALL count/padding classes in proved bounds."""
from pathlib import Path
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from collections import Counter
import argparse,json,time,hashlib
ROOT=Path(__file__).resolve().parent


def main():
    p=argparse.ArgumentParser();p.add_argument('--max-capacity',type=int,default=32)
    B=p.parse_args().max_capacity;start=time.monotonic();counts=Counter();rows=[]
    for L in range(3,B+1):
        H=L+2;c=Counter();digest=hashlib.sha256();minC=None;minLC=None
        for h in range(1,H+1):
            N=2*h+L
            for alpha in range(1,h+L+1):
                F=arm_prefix(alpha,[2]*h+[L],N+1)
                D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,N+2)]
                R=next(n for n in range(2,N+2) if not D[n])-1
                assert R<=N and all(D[n]>0 for n in range(2,R+1))
                assert all(x==0 for x in D[R+1:])
                G=[];s=0
                for x in F:s+=x;G.append(s)
                best=None
                for n in range(4,R+1):
                    k=n-3
                    if best is None or G[k]*best[1]<best[0]*G[k-1]:best=(G[k],G[k-1])
                    slack=best[0]*D[n-1]-best[1]*D[n]
                    assert slack>=0,(L,h,alpha,n,slack)
                    c['ALL_current_ranks_envelope_checked']+=1
                    c['ALL_shift_comparisons_covered']+=k
                    minC=slack if minC is None else min(minC,slack)
                if h==H:
                    for n in range(h+2,R+1):
                        minor=D[n]**2-D[n-1]*D[n+1]
                        assert minor>=0,(L,h,alpha,n,minor)
                        c['ALL_full_tail_base_minors']+=1
                        minLC=minor if minLC is None else min(minLC,minor)
                    c['ALL_full_tail_base_padding_classes']+=1
                digest.update((json.dumps([L,h,alpha,R,F],separators=(',',':'))+'\n').encode())
                c['ALL_actual_entrance_words']+=1
        row=dict(L=L,H=H,counts=dict(c),all_actual_prefix_sha256=digest.hexdigest(),
                 minimum_C_envelope_slack=minC,minimum_LC_base_minor=minLC)
        counts.update(c);rows.append(row)
        print(json.dumps(dict(L=L,words=c['ALL_actual_entrance_words'],seconds=time.monotonic()-start)),flush=True)
    out=dict(status='COMPLETE_FIXED_CAPACITY_ONE_JUMP_C_ENTRANCE',max_capacity=B,counts=dict(counts),rows=rows,
        seconds=time.monotonic()-start,
        scope='Complete h<=L+2,alpha<=h+L entrance and full positive-D-tail LC baseh=L+2. Needs independent actual closed-form rebuild and unbounded tail/C/alpha-clamp assembly. Not arbitrary L or original UI.')
    (ROOT/'one_jump_fixed_capacity_C_entrance.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='rows'}),flush=True)


if __name__=='__main__':main()
