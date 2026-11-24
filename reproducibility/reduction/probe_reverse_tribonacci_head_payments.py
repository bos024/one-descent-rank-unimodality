"""Exact first TWO quotient minors under the complete small-remainder box."""
from pathlib import Path
from fractions import Fraction as F
import json
from probe_tribonacci_inverse_bernstein_corners import const,add,sub,mul,sc,powp,var,bernstein,sign
from probe_reverse_tribonacci_bernstein_corners import substitute
ROOT=Path(__file__).resolve().parent
def main():
    a=const(-1,1);b=const(-1,-1,1);w=var(0);r=var(1);R0=var(2);R1=var(3)
    J0=sub(const(1),R0);J1=sub(sub(w,mul(a,J0)),R1)
    e2=add(sc(sub(mul(w,w),w),F(1,2)),r)
    e3=add(sc(mul(mul(w,sub(w,const(1))),sub(w,const(2))),F(1,6)),mul(r,sub(w,const(1))))
    J2=sub(sub(e2,mul(a,J1)),mul(b,J0));J3=sub(sub(e3,mul(a,J2)),mul(b,J1))
    polys={'J0_positive':J0,'J1_positive':J1,'J2_positive':J2,
      'first_LC_minor':sub(powp(J1,2),mul(J0,J2)),
      'second_LC_minor':sub(powp(J2,2),mul(J1,J3))}
    result={}
    for base in [12,18]:
        W=add(const(base),var(0));vals=[W,mul(var(1),W),add(const(-F(1,4)),sc(var(2),F(1,2))),add(const(-F(1,4)),sc(var(3),F(1,2)))]
        entries={}
        for name,p in polys.items():
            p=substitute(p,vals);byX={}
            for k,v in p.items():byX.setdefault(k[0],{})[k[1:]]=v
            rows=[];neg=[];strict=True
            for n,pj in sorted(byX.items()):
                for k,v in bernstein(pj):
                    sg=sign(v);row=dict(X_power=n,box_index=k,coefficient=list(map(str,v)));rows.append(row)
                    if sg<0:neg.append(row)
                    if n==0 and sg<=0:strict=False
            entries[name]=dict(count=len(rows),negative_count=len(neg),first_negative=neg[:1],strict_constant_positive=strict)
            if base==12:entries[name]['complete_coefficient_data']=rows
        result[str(base)]=entries
    out=dict(status='EXACT_REVERSE_HEAD_DIAGNOSTIC_ONLY',cases=result)
    (ROOT/'probe_reverse_tribonacci_head_payments.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:{n:{a:b for a,b in v.items() if a!='complete_coefficient_data'} for n,v in es.items()} for k,es in result.items()}))
if __name__=='__main__':main()
