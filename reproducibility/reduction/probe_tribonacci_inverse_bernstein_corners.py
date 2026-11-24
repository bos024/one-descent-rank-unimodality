"""Exact unbounded-cone diagnostic for the THREE quadratic-inverse corner minors."""
from pathlib import Path
from fractions import Fraction as F
from math import comb,lcm
from itertools import product
import json,time
from probe_tribonacci_quadratic_inverse import mul as fm,sign as fs
ROOT=Path(__file__).resolve().parent
ZERO=(F(0),)*3
def fa(a,b):return tuple(x+y for x,y in zip(a,b))
def const(a,b=0,c=0):
    q=(F(a),F(b),F(c));return {(0,0,0,0):q} if q!=ZERO else {}
def add(a,b):
    c=dict(a)
    for k,v in b.items():c[k]=fa(c.get(k,ZERO),v)
    return {k:v for k,v in c.items() if v!=ZERO}
def sc(a,s):return {k:tuple(s*x for x in v) for k,v in a.items() if s and v!=ZERO}
def sub(a,b):return add(a,sc(b,-1))
def mul(a,b):
    c={}
    for i,x in a.items():
        for j,y in b.items():
            k=tuple(p+q for p,q in zip(i,j));c[k]=fa(c.get(k,ZERO),fm(x,y))
    return {k:v for k,v in c.items() if v!=ZERO}
def powp(a,n):
    p=const(1)
    for j in range(n):p=mul(p,a)
    return p
def var(n):
    key=tuple(int(j==n) for j in range(4));return {key:(F(1),F(0),F(0))}
def subst(a,values):
    pre=[[powp(v,k) for k in range(6)] for v in values];out={}
    for key,c in a.items():
        t=const(*c)
        for j,n in enumerate(key):t=mul(t,pre[j][n])
        out=add(out,t)
    return out
def sign(a):
    d=lcm(*(x.denominator for x in a));return fs(tuple(int(d*x) for x in a))
def bernstein(poly):
    degree=tuple(max((k[j] for k in poly),default=0) for j in range(3));rows=[]
    for k in product(*(range(d+1) for d in degree)):
        v=ZERO
        for alpha,c in poly.items():
            if all(a<=b for a,b in zip(alpha,k)):
                s=F(1)
                for a,b,d in zip(alpha,k,degree):s*=F(comb(b,a),comb(d,a))
                v=fa(v,tuple(s*x for x in c))
        rows.append((k,v))
    return rows
def main():
    start=time.monotonic();lam=const(0,1);a=const(-1,1);w=var(0);r=var(1);x0=var(2);x1=var(3)
    x2=mul(lam,sub(sub(const(1),mul(a,x1)),x0))
    x3=mul(lam,sub(sub(w,mul(a,x2)),x1))
    e2=add(sc(sub(mul(w,w),w),F(1,2)),r)
    x4=mul(lam,sub(sub(e2,mul(a,x3)),x2))
    e3=add(sc(mul(mul(w,sub(w,const(1))),sub(w,const(2))),F(1,6)),mul(r,sub(w,const(1))))
    x5=mul(lam,sub(sub(e3,mul(a,x4)),x3))
    binary=sub(powp(add(x2,x3),2),mul(add(x1,x2),add(x3,x4)))
    ternary0=sub(powp(add(add(x2,x3),x4),2),mul(add(add(x1,x2),x3),add(add(x3,x4),x5)))
    ternary1=sub(powp(add(add(x1,x2),x3),2),mul(add(add(x0,x1),x2),add(add(x2,x3),x4)))
    polynomials={'binary_last_minor':binary,'ternary_penultimate_minor':ternary0,'ternary_last_minor':ternary1,
       'binary_last_value':add(x1,x2),'ternary_penultimate_value':add(add(x1,x2),x3),'ternary_last_value':add(add(x0,x1),x2)}
    results={}
    for base,box in [(18,F(1,4)),(24,F(1,8)),(32,F(1,16)),(64,F(1,32))]:
        W=add(const(base),var(0));R=mul(var(1),W)
        values=[W,R,add(const(-box),sc(var(2),2*box)),add(const(-box),sc(var(3),2*box))]
        entries={}
        for name,poly in polynomials.items():
            p=subst(poly,values);byX={}
            for k,c in p.items():byX.setdefault(k[0],{})[k[1:]]=c
            neg=[];count=0;constant_positive=True;coeff_data=[]
            for j,q in sorted(byX.items()):
                for k,c in bernstein(q):
                    s=sign(c);count+=1
                    coeff_data.append(dict(X_power=j,box_index=k,coefficient=list(map(str,c))))
                    if s<0:neg.append(dict(X_power=j,box_index=k,coefficient=list(map(str,c))))
                    if j==0 and s<=0:constant_positive=False
            entries[name]=dict(negative_count=len(neg),first_negative=neg[:2],Bernstein_coefficients=count,strict_constant_positive=constant_positive)
            if base==18:entries[name]['complete_coefficient_data']=coeff_data
        results[str(base)+'_'+str(box)]=entries
    out=dict(status='EXACT_BERNSTEIN_DIAGNOSTIC_ONLY',cases=results,seconds=time.monotonic()-start)
    (ROOT/'probe_tribonacci_inverse_bernstein_corners.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(status=out['status'],cases={k:{name:{a:b for a,b in e.items() if a!='complete_coefficient_data'} for name,e in es.items()} for k,es in results.items()},seconds=out['seconds'])),flush=True)
if __name__=='__main__':main()
