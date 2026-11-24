"""Exact full positive-primitive head cone, including the initial atom."""
from pathlib import Path
from fractions import Fraction as F
import json
from probe_tribonacci_inverse_bernstein_corners import const,add,sub,mul,sc,powp,var,bernstein,sign
from probe_reverse_tribonacci_bernstein_corners import substitute,binom_poly
from probe_tribonacci_quadratic_inverse import sign as fsign,sub as fsub,mul as fmul,ZERO
ROOT=Path(__file__).resolve().parent
def main():
    a=const(-1,1);b=const(-1,-1,1);w=var(0);r=var(1);R0=var(2);R1=var(3)
    J=[sub(const(1),R0)];J.append(sub(sub(w,mul(a,J[0])),R1))
    for n in range(2,5):
        e={}
        for k in range(n//2+1):e=add(e,mul(binom_poly(r,k),binom_poly(sub(w,const(k)),n-2*k)))
        J.append(sub(sub(e,mul(a,J[-1])),mul(b,J[-2])))
    D=[J[0]]+[sub(J[n],J[n-1]) for n in range(1,5)]
    polys={'D'+str(n)+'_positive':p for n,p in enumerate(D)}
    polys.update({'primitive_minor'+str(n):sub(powp(D[n],2),mul(D[n-1],D[n+1])) for n in range(1,4)})
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
    data=json.loads((ROOT/'tribonacci_rich_reverse_certificate_data.json').read_text());fail=[];reads=0
    for row in data['contexts']:
        # FULL primitive including D0=J0, also for the pure entrance.
        j=list(map(tuple,row['J']));d=[]
        for n,v in enumerate(j):
            q=fsub(v,j[n-1] if n else ZERO);d.append(q if fsign(q)>0 else ZERO)
        for n in range(1,len(d)-1):
            m=fsub(fmul(d[n],d[n]),fmul(d[n-1],d[n+1]));reads+=1
            if fsign(m)<0:fail.append(dict(u=row['u'],r=row['r'],n=n,margin=m))
    out=dict(status='EXACT_PRIMITIVE_HEAD_DIAGNOSTIC_ONLY',cases=result,complete31base_primitive_failures=fail,complete31base_primitive_minors=reads)
    (ROOT/'probe_tribonacci_quotient_primitive_head.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(cases={k:{n:{a:b for a,b in v.items() if a!='complete_coefficient_data'} for n,v in es.items()} for k,es in result.items()},base_failures=fail,base_minors=reads)),flush=True)
if __name__=='__main__':main()
