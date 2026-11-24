"""Exact independent finite-series checks of the unbounded-arm source proof."""
from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT))
from audit_large_peak_skeleton import arm,fastconv,at,window,add

def renewal(t,N):
    f=[1]
    for n in range(1,N+1):f.append(sum(at(f,n-i) for i in range(1,t+1)))
    return f

def main():
    N=65;profiles=source_checks=identity_checks=finite_checks=0
    for t in range(1,11):
        for s in range(1,11):
            A,B=renewal(t,N),renewal(s,N)
            P=fastconv(A,B)
            for M in range(max(t,s)+1,t+s+7):
                H=add(A,B,[0]+window(P,M),[-x for x in P])[:N+1]
                for n in range(3,N+1):
                    u=H[n]-H[n-1];prev=H[n-1]-H[n-2]
                    source=at(P,n-t-s-2)+at(P,n-M-1)-2*at(P,n-M-2)
                    assert 2*prev-u==source;identity_checks+=1
                    assert source>=0;source_checks+=1
                profiles+=1
                if t<=4 and s<=4 and M==max(t,s)+1:
                    h,k=14,17
                    AF,BF=arm(t,[t]*(h-1)),arm(s,[s]*(k-1))
                    PF=fastconv(AF,BF)
                    HF=add(AF,BF,[0]+window(PF,M),[-x for x in PF])
                    for n in range(min(h,k)+1):
                        assert HF[n]==H[n];finite_checks+=1
    out=dict(status='PASS',scope='Finite diagnostics of the complete unbounded formal-series source proof and its exact finite initial range. No central finite-arm theorem inferred.',
             profiles=profiles,actual_source_comparisons=source_checks,
             exact_source_identities=identity_checks,finite_arm_coefficient_equalities=finite_checks)
    ROOT.joinpath('audit_unbounded_arm_bulk_source.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)

if __name__=='__main__':main()
