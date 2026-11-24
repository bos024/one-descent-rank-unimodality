"""Exact Q(lambda3) prefix tests. Real-root intervals certified by integer cubic."""
from pathlib import Path
import json,time
ROOT=Path(__file__).resolve().parent
ONE=(1,0,0);ZERO=(0,0,0);A=(-1,1,0);B=(-1,-1,1)
def add(x,y):return tuple(a+b for a,b in zip(x,y))
def sub(x,y):return tuple(a-b for a,b in zip(x,y))
def power(x,n):
    v=ONE
    while n:
        if n&1:v=mul(v,x)
        x=mul(x,x);n//=2
    return v
def mul(x,y):
    p=[0]*5
    for i,a in enumerate(x):
        for j,b in enumerate(y):p[i+j]+=a*b
    return(p[0]+p[3]+p[4],p[1]+p[3]+2*p[4],p[2]+p[3]+2*p[4])
INTERVALS={}
def interval(bits):
    if bits not in INTERVALS:
        M=1<<bits;lo=M;hi=2*M
        while hi-lo>1:
            m=(lo+hi)//2;v=m*m*m-m*m*M-m*M*M-M*M*M
            if v<0:lo=m
            else:hi=m
        INTERVALS[bits]=(lo,hi,M)
    return INTERVALS[bits]
def sign(x):
    if x==ZERO:return 0
    bits=max(128,((2*max(abs(a).bit_length() for a in x)+100+127)//128)*128)
    while True:
        lo,hi,M=interval(bits);l=x[0]*M*M;h=l
        for c,a,b in [(x[1],lo*M,hi*M),(x[2],lo*lo,hi*hi)]:
            l+=c*(a if c>=0 else b);h+=c*(b if c>=0 else a)
        if l>0:return 1
        if h<0:return -1
        bits*=2
def pc(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c
def inverse(E):
    f=[]
    for n,e in enumerate(E):
        v=(e,0,0)
        if n:v=sub(v,mul(A,f[-1]))
        if n>=2:v=sub(v,mul(B,f[-2]))
        f.append(v)
    return f
def terminal_norm(f):
    e0=f[-1];e1=f[-2] if len(f)>1 else ZERO
    return add(add(mul(e0,e0),mul(A,mul(e0,e1))),mul(B,mul(e1,e1)))
def main():
    start=time.monotonic();K=[1,3,5,5,3,1];E=[1];rows=[]
    for v in range(1,101):
        E=pc(E,K);f=inverse(E);D=len(E)-1
        assert terminal_norm(f)==mul(power(A,2*v),power(sub(ONE,A),2*v))
        negpos=[i for i in range(D-1) if sign(f[i])<=0]
        neglc=[i for i in range(1,D-2) if sign(sub(mul(f[i],f[i]),mul(f[i-1],f[i+1])))<0]
        rows.append(dict(v=v,negative_prefix_positions=negpos,negative_prefix_minors=neglc,terminal_signs=[sign(a) for a in f[-3:]]))
    pure=[];mixedbad=[]
    for u in range(0,15):
        for r in range(0,25):
            if not u+r:continue
            E=[1]
            for t in [2]*u+[3]*r:E=pc(E,[1]*t)
            f=inverse(E);D=len(E)-1
            assert terminal_norm(f)==mul(power(A,2*u),power(sub(ONE,A),r))
            badp=[i for i in range(max(0,D-1)) if sign(f[i])<=0]
            badm=[i for i in range(1,D-2) if sign(sub(mul(f[i],f[i]),mul(f[i-1],f[i+1])))<0]
            if u==0:pure.append(dict(r=r,nonpositive=badp,negative_minors=badm))
            elif badp or badm:mixedbad.append(dict(u=u,r=r,nonpositive=badp,negative_minors=badm))
    out=dict(status='EXACT_ALGEBRAIC_DIAGNOSTIC_ONLY',diagonal=rows,pure=pure,mixed_failures=mixedbad,seconds=time.monotonic()-start)
    (ROOT/'probe_tribonacci_quadratic_inverse.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(status=out['status'],diagonal_failures=[r for r in rows if r['negative_prefix_positions'] or r['negative_prefix_minors']],pure=pure,mixed_failures=mixedbad,seconds=out['seconds'])),flush=True)
if __name__=='__main__':main()
