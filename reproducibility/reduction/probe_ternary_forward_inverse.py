"""Exact coefficient diagnostics for forward inverse CI prefixes."""
from pathlib import Path
import sys,json,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_arbitrary_Fibonacci_tail_late_C import sign,add,sub,mul
Q=(-1,1);PHI=(0,1);ONE=(1,0);ZERO=(0,0)
def kernel(u,r):
    E=[1]
    for width in [2]*u+[3]*r:
        E=[sum(E[max(0,k-width+1):min(k+1,len(E))]) for k in range(len(E)+width-1)]
    return E
def forward(E):
    p=ZERO;out=[]
    for e in E:p=sub((e,0),mul(Q,p));out.append(p)
    return out
def main():
    bad=[];ct=0;sha=hashlib.sha256();pure=[]
    for u in range(81):
        for r in range(101):
            if u+r==0:continue
            E=kernel(u,r);a=forward(E)
            assert all(sign(x)>0 for x in a)
            neg=[n for n in range(1,len(a)-1) if sign(sub(mul(a[n],a[n]),mul(a[n-1],a[n+1])))<0]
            if u and neg:bad.append((u,r,neg[:5]))
            if u==0 and r<15:pure.append((r,neg))
            if u:
                ct+=len(a)-2
                sha.update(str((u,r,a[-1])).encode())
    out=dict(status='EXACT_DIAGNOSTIC_ONLY',mixed_failures=bad,pure_three=pure,comparisons=ct,state_sha256=sha.hexdigest())
    (ROOT/'probe_ternary_forward_inverse.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
