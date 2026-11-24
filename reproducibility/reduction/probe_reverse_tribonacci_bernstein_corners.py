"""Reverse denominator: exact generic small-terminal-norm cone corners."""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import json,time
from probe_tribonacci_inverse_bernstein_corners import const,add,sub,mul,sc,powp,var,subst,bernstein,sign
ROOT=Path(__file__).resolve().parent
def binom_poly(p,k):
    out=const(F(1,factorial(k)))
    for j in range(k):out=mul(out,sub(p,const(j)))
    return out
def substitute(p,vals):
    powers=[[powp(v,k) for k in range(1+max((i[j] for i in p),default=0))] for j,v in enumerate(vals)]
    out={}
    for key,c in p.items():
        term=const(*c)
        for j,k in enumerate(key):term=mul(term,powers[j][k])
        out=add(out,term)
    return out
def main():
    start=time.monotonic();a=const(-1,1);b=const(-1,-1,1);w=var(0);r=var(1);x=[var(2),var(3)]
    for k in range(2,8):
        t=k-2;head={}
        for j in range(t//2+1):head=add(head,mul(binom_poly(r,j),binom_poly(sub(w,const(j)),t-2*j)))
        x.append(sub(sub(mul(b,head),mul(a,x[-1])),mul(b,x[-2])))
    s=lambda *inds:sum_poly([x[i] for i in inds])
    cases={'binary_last_minor':sub(powp(s(4,5),2),mul(s(3,4),s(5,6))),
      'ternary_penultimate_minor':sub(powp(s(4,5,6),2),mul(s(3,4,5),s(5,6,7))),
      'ternary_last_minor':sub(powp(s(3,4,5),2),mul(s(2,3,4),s(4,5,6))),
      'binary_last_value':s(3,4),'ternary_penultimate_value':s(3,4,5),'ternary_last_value':s(2,3,4)}
    results={}
    for base,box in [(18,F(1,4)),(24,F(1,4)),(32,F(1,4))]:
        W=add(const(base),var(0));R=mul(var(1),W)
        vals=[W,R,add(const(-box),sc(var(2),2*box)),add(const(-box),sc(var(3),2*box))]
        entries={}
        for name,p in cases.items():
            after=substitute(p,vals);byX={}
            for k,c in after.items():byX.setdefault(k[0],{})[k[1:]]=c
            rows=[];neg=[];strict=True
            for j,pj in sorted(byX.items()):
                for k,c in bernstein(pj):
                    sg=sign(c);row=dict(X_power=j,box_index=k,coefficient=list(map(str,c)));rows.append(row)
                    if sg<0:neg.append(row)
                    if j==0 and sg<=0:strict=False
            entries[name]=dict(negative_count=len(neg),first_negative=neg[:2],strict_constant_positive=strict,count=len(rows))
            if base==18:entries[name]['complete_coefficient_data']=rows
        results[str(base)]=entries
    out=dict(status='EXACT_REVERSE_QUADRATIC_CORNER_DIAGNOSTIC_ONLY',cases=results,seconds=time.monotonic()-start)
    (ROOT/'probe_reverse_tribonacci_bernstein_corners.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(status=out['status'],cases={k:{n:{a:b for a,b in v.items() if a!='complete_coefficient_data'} for n,v in e.items()} for k,e in results.items()},seconds=out['seconds'])),flush=True)
def sum_poly(rows):
    out={}
    for p in rows:out=add(out,p)
    return out
if __name__=='__main__':main()
