"""Exact QA of the all-four-count actual theorem, not finite proof premises."""
from pathlib import Path
from collections import Counter
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_binary_ternary_A2_original_family import arm,examine,core_rel,window
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256()
    for r in [50,51,52,53,54,55,60,72,100]:
        s0=(r+4)//3;assert s0>=18 and r+2<=3*s0<=r+4
        for s in list(range(0,51))+[75,100,150]:
            for alpha in [1,2,4,11,60]:
                F=arm(alpha,[3]*r+[4]*s);Z=F+[0,0];G=[];v=0
                for x in Z:v+=x;G.append(v)
                d=[max(0,Z[n]-Z[n-1]) if n>=2 else 0 for n in range(len(Z))]
                starts=[]
                if r+4>=3*s:starts.append(('near_phase',r+s+2))
                if s>=s0:starts.append(('four_phase',s+4))
                assert starts
                for kind,A in starts:
                    for n in range(A,len(Z)-1):
                        assert Z[n]**2>=Z[n-1]*Z[n+1],(alpha,r,s,kind,n)
                        ct[kind+'_ENTIRE_ordinary_tail_minors']+=1
                worst=1
                for N in range(4,len(Z)):
                    k=N-3
                    if G[k]*G[worst-1]<G[worst]*G[k-1]:worst=k
                    assert G[worst]*d[N-1]>=G[worst-1]*d[N],(alpha,r,s,N)
                    ct['actual_complete_C_worst_prefix_reads']+=1;ct['logical_ALLshift_C_comparisons']+=k
                ct['actual_ALLfour_count_hosts']+=1
                if r<3*s+8:ct['hosts_OUTSIDE_old_ternary_surplus']+=1
                if s==s0:ct['analytic_MOVING_diagonal_seed_QA_hosts']+=1
                sha.update(str((alpha,r,s,F[-4:])).encode())
    print(json.dumps(dict(phase='all_actual_C_and_ordinary',counts=dict(ct))),flush=True)
    profiles=[(a,[3]*r+[4]*s) for r,s in [(50,1),(50,20),(50,40),(51,18),(55,45),(60,80)] for a in [1,3]]
    others=[(1,[2]*4+[3]*5),(2,[2]*2+[4]*6),(1,[2]*2+[7,9]),(2,[3]*32+[4]*3)]
    for i,(a,U) in enumerate(profiles):
        for b,V in profiles[:4]+others:
            A,B=arm(a,U),arm(b,V);examine(A,B,ct,sha,True)
            core_rel(A,B,max(U+V+[1])+1,ct,sha,'A7_ALLfour_ORIGINAL')
        b,V=others[i%len(others)];A,B=arm(a,U),arm(b,V)
        t=max(4,len(B)-len(A),12+i*3);X=[1]+window(A,t)
        examine(X,B,ct,sha,False);core_rel(X,B,max(t,max(V))+1,ct,sha,'A7_heavier_append_ORIGINAL')
    out=dict(status='EXACT_QA_PASS_ALL_ALPHA_ALL_FOUR_COUNTS_AT_THREE_COUNT_AT_LEAST_FIFTY',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      scope='ALLalpha>=1/r>=50/ALLs>=0 ACTUALFULLC proofbyanalyticMOVINGdiagonalseed+whole4heredity+nearcubiccut. NOnewfinitepremise. ORIGINALA7NOcount-ratio. Generaloriginal/C/A2andremainingr<50/binaryprefixmixedOPEN.')
    (ROOT/'audit_three_four_all_four_counts.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
