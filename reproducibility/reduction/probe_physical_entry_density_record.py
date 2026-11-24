"""Unregistered exact diagnostics of density hypotheses at a strictly growing physical entrance."""
from pathlib import Path
import sys,json,time
from random import Random
from collections import Counter
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import rebuild
def main():
    rng=Random(20261031361);ct=Counter();bad={};start=time.monotonic()
    for _ in range(2200):
        V=sorted(rng.choices(range(3,38),k=rng.randint(2,10)));h=sum(t-1 for t in V);W=sum(V)
        u=rng.randint(max(1,(h+1)//3),h-1);R=rebuild(V,W+1);r=[0,0]+[R[n]-R[n-1] for n in range(2,len(R))]
        for alpha in {1,3,h+u+2}:
            F=arm_prefix(alpha,[2]*u+V,W+1);D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
            A,B=D[W:W+2]
            if not B>A>0:continue
            ct['strict_physical_entrances']+=1
            cnum=B*r[W];cden=A*r[W+1]
            if cnum>cden:bad.setdefault('current_density_ratio_exceeds_one',dict(alpha=alpha,u=u,V=V))
            for j in range(3,W+1):
                if cnum*D[j-1]*r[j]>cden*D[j]*r[j-1]:
                    bad.setdefault('current_density_ratio_not_record_minimum',dict(alpha=alpha,u=u,V=V,current=W+1,past=j,actual_pair=[A,B]))
                ct['current_record_prefix_comparisons']+=1
            for j in range(3,W+1):
                val=D[j]**2*r[j-1]*r[j+1]-D[j-1]*D[j+1]*r[j]**2
                if val<0:
                    bad.setdefault('full_relative_LC_despite_growing_physical_entry',dict(alpha=alpha,u=u,V=V,centre=j,physical_current=W+1,actual_triple=D[j-1:j+2]))
                ct['full_relative_density_centres']+=1
            ct['actual_hosts']+=1
        if len(bad)>=3:break
    out=dict(status='FINITE_DIAGNOSTICS_ONLY_NO_DENSITY_THEOREM',counts=dict(ct),counterexamples=bad,seconds=time.monotonic()-start)
    (ROOT/'probe_physical_entry_density_record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()

