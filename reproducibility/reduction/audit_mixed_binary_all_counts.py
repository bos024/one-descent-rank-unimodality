"""Finite exact QA of the all-binary-count analytic theorem. No finite premise."""
from pathlib import Path
from collections import Counter
import sys,json,hashlib,time
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_binary_first_defect_ordinary_tail import arm
from audit_mixed_binary_reference_ordinary import full_C,at
from verify_binary_ternary_A2_original_family import check,core,greedy_ideal,UI

def main():
    start=time.monotonic();ct=Counter();sha=hashlib.sha256()
    for r in [57,58,63,90]:
        for u in [1,2,3,5,2*r-1,2*r,2*r+1,2*r+2,2*r+3,2*r+15,3*r,4*r]:
            s0=0 if u<=2*r else (u-2*r)//3+1
            fourcounts=sorted(set([0,1,2,4,8,17,18,25,50,max(0,s0-1),s0,s0+1]))
            for s in fourcounts:
                for alpha in [1,2,9]:
                    f=arm(alpha,[2]*u+[3]*r+[4]*s);h=2*r+3*s;W=3*r+4*s;A=r+s+3
                    full_C(f,len(f)-2,ct,'all_binary_actual')
                    if u<=h:
                        for n in range(A,len(f)-1):
                            assert f[n]**2>=f[n-1]*f[n+1],(alpha,u,r,s,n)
                            ct['entire_ordinary_tail_minors']+=1
                    else:
                        margin=f[W+1]**2-f[W]*f[W+2]
                        assert margin==-(4**r)*(5**s),(alpha,u,r,s,margin)
                        ct['exact_sharp_negative_ordinary_controls']+=1
                    seed=arm(alpha,[2]*u)
                    h3=[1,1,2,4,7,13,24]
                    jets=[h3[n]-at(seed,n) for n in range(3,7)]
                    assert all(x>=y for x,y in zip(jets,[1,2,5,11]))
                    ct['all_finite_binary_seed_jet_rows']+=1
                    ct['actual_all_count_hosts']+=1
                    sha.update(str((alpha,u,r,s,f,jets)).encode())
    for case in range(24):
        r=57+case%3;s=1+case%7;u=[1,2,3,2*r+1][case%4];a=1+case%3
        U=[2]*u+[3]*r+[4]*s;X=arm(a,U)[:-2]
        rr=57;ss=1+case%3;uu=[1,3,2*rr+1][case%3];V=[2]*uu+[3]*rr+[4]*ss;b=1
        Y=arm(b,V)[:-2]
        check(X,Y,ct,sha,True)
        M=5+case%4;H,L,R=core(X,Y,M)
        host=[1]*a+U+[M]+list(reversed([1]*b+V));actual=greedy_ideal(host)
        assert H==actual and UI(actual)
        ct['TRUE_greedy_ORIGINAL_arbitrary_binary_mixed_pairs']+=1
        ct['TRUE_greedy_ORIGINAL_rank_counts']+=len(actual)
        sha.update(str((host,actual)).encode())
    out=dict(status='PASS_EXACT_QA_ALL_BINARY_FOUR_COUNTS_FROM_FIFTY_SEVEN_THREES',counts=dict(ct),
        sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        scope='Finite QA only; NOnewfiniteproofpremise. Analytic arbitraryseed/fourheredity/movingfirstcrossing proves full stated all-count theorem. General conjecture OPEN.')
    (ROOT/'audit_mixed_binary_all_counts.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)
if __name__=='__main__':main()
