"""Separate exact QA. Complete proof inputs are in the deterministic builder."""
from pathlib import Path
from collections import Counter
from random import Random
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_binary_first_defect_ordinary_tail import arm
from audit_mixed_binary_reference_ordinary import full_C
from verify_binary_ternary_A2_original_family import check,core,greedy_ideal,UI

def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=Random(402771)
    for r in [0,1,2,3,4,5,6,7,8,11,20,56,57]:
        us=sorted(set([0,1,2,3,5,7,max(0,2*r-1),2*r,2*r+1,3*r+7]))
        for u in us:
            cross=0 if u<=2*r else (u-2*r)//3+1
            ss=sorted(set([0,1,2,3,5,17,18,25,cross,max(0,cross-1),cross+1]))
            for s in ss:
                for alpha in [1,2,9]:
                    f=arm(alpha,[2]*u+[3]*r+[4]*s)
                    full_C(f,len(f)-2,ct,'complete_capacity_four_actual')
                    ct['all_alphabet_actual_QA_hosts']+=1
                    sha.update(str((alpha,u,r,s,f)).encode())
    for case in range(120):
        a,b=rng.randint(1,5),rng.randint(1,5)
        U=[2]*rng.randint(0,18)+[3]*rng.randint(0,12)+[4]*rng.randint(0,12)
        V=[2]*rng.randint(0,18)+[3]*rng.randint(0,12)+[4]*rng.randint(0,12)
        X,Y=arm(a,U)[:-2],arm(b,V)[:-2]
        check(X,Y,ct,sha,bool(U and V))
        M=5+case%6;H,L,R=core(X,Y,M)
        host=[1]*a+U+[M]+list(reversed([1]*b+V));actual=greedy_ideal(host)
        assert actual==H and UI(actual)
        ct['TRUE_greedy_ORIGINAL_all_capacity_four_pairs']+=1
        ct['TRUE_greedy_ORIGINAL_rank_counts']+=len(actual)
        sha.update(str((host,actual)).encode())
    # The exceptional ordinary comparison really fails; its C remains true.
    f=arm(7,[2]*7+[3]+[4]);assert f[5]**2-f[4]*f[6]==-7
    full_C(f,len(f)-2,ct,'negative_ordinary_control')
    out=dict(status='PASS_EXACT_QA_COMPLETE_CAPACITY_FOUR_C_AND_ORIGINAL_FAMILY',counts=dict(ct),
        sha256=sha.hexdigest(),seconds=time.monotonic()-st,
        scope='Separate finite QA only. The 3059 kernelchecked deterministic margins are the EXPLICIT complete finite proof inputs; these extra hosts are not proof premises. General original conjecture OPEN.')
    (ROOT/'audit_complete_capacity_four.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
