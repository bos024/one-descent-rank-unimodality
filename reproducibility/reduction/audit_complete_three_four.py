"""Additional exact actual/original QA. COMPLETE proof bases are verified separately."""
from pathlib import Path
from collections import Counter
from random import Random
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_binary_ternary_A2_original_family import arm,examine,core_rel,window
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=Random(110104)
    profiles=[(a,r,s) for r in range(0,18) for s in [0,1,3,8,18,35,80] for a in [1,2,7]]
    profiles += [(rng.randint(1,150),rng.randint(0,80),rng.randint(0,150)) for _ in range(700)]
    for alpha,r,s in profiles:
        F=arm(alpha,[3]*r+[4]*s)+[0,0];G=[];v=0
        for x in F:v+=x;G.append(v)
        d=[max(0,F[n]-F[n-1]) if n>=2 else 0 for n in range(len(F))]
        worst=1
        for N in range(4,len(F)):
            k=N-3
            if G[k]*G[worst-1]<G[worst]*G[k-1]:worst=k
            assert G[worst]*d[N-1]>=G[worst-1]*d[N],(alpha,r,s,N,worst)
            ct['ALLcurrent_COMPLETEworst_prefix_C_reads']+=1;ct['logical_ALLshift_C_reads']+=k
        ct['ALLcount_actual_three_four_hosts']+=1
        if r<50 and s>18:ct['SMALLthree_UNBOUNDEDfour_QA_hosts']+=1
        sha.update(str((alpha,r,s,F[-4:])).encode())
    news=[(a,[3]*r+[4]*s) for r,s in [(1,20),(2,35),(4,50),(8,30),(15,3),(25,80),(40,40)] for a in [1,5]]
    olds=[(1,[2]*4+[3]*5),(2,[2]*3+[4]*6),(1,[2]*2+[6,9]),(3,[3]*3+[18])]
    for i,(a,U) in enumerate(news):
        for b,V in news[:4]+olds:
            A,B=arm(a,U),arm(b,V);examine(A,B,ct,sha,bool(U and V))
            core_rel(A,B,max(U+V+[1])+1,ct,sha,'A8_ALLthree_four_ORIGINAL')
        b,V=olds[i%len(olds)];A,B=arm(a,U),arm(b,V);t=max(4,len(B)-len(A),10+4*i)
        X=[1]+window(A,t);examine(X,B,ct,sha,False)
        core_rel(X,B,max(t,max(V))+1,ct,sha,'A8_heavier_append_ORIGINAL')
    out=dict(status='EXACT_QA_PASS_COMPLETE_ACTUAL_THREE_FOUR_C_AND_A8_ORIGINAL_FAMILY',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      scope='ALLalpha/r/s actualcompleteC proofusesanalyticr>=50+COMPLETE96ordinaryentrances/207propercutpredicates/224oldpairs,thenWHOLEfourheredity. ALLthree/fourcountsunrestricted. A8ORIGINALcore/BOTHrelativesANYstrictpeak+ONEheavierappend. ThisextraQAisNOTfinitepremise. Binaryprefixu>=1/generaloriginal/C/A2remainOPEN.')
    (ROOT/'audit_complete_three_four.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
