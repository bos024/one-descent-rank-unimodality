"""Complete diagonal entrance: every4<=u<=32 and every relevant padding."""
from pathlib import Path
import sys,json,hashlib,time
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix

def main():
    start=time.monotonic();contexts=[];unique=set();checks=0;sha=hashlib.sha256()
    for u in range(4,33):
        r=2*u;clamp=r+u//2;B=(3*u+4*r)//2
        for alpha in range(1,clamp+1):
            F=arm_prefix(alpha,[2]*u+[3]*r,alpha+2*u+3*r+1)
            D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];ell=D.index(max(D))
            assert ell<=B
            margins=[]
            for n in range(r+3,ell):
                M=D[n]**2-D[n-1]*D[n+1]-D[n];assert M>=0,(u,r,alpha,n)
                unique.add(M);margins.append(M);checks+=1
            row=dict(u=u,r=r,alpha=alpha,clamp=clamp,first_mode=ell,margins=margins)
            contexts.append(row);sha.update(json.dumps(row,separators=(',',':')).encode())
    values=sorted(unique);parts=[];lines=['import Mathlib','set_option maxHeartbeats 0','set_option maxRecDepth 100000','namespace TernaryRichDiagonalCertificate','']
    for p,startidx in enumerate(range(0,len(values),300)):
        name='part'+str(p);parts.append(name)
        lines += ['def '+name+' : List ℤ := ['+', '.join(map(str,values[startidx:startidx+300]))+']',
          'theorem '+name+'_certificate : '+name+'.all (fun z => decide (0 ≤ z)) = true := by decide','']
    lines += ['def rows : List ℤ := '+' ++ '.join(parts),'',
      'theorem all_diagonal_integer_margins : rows.all (fun z => decide (0 ≤ z)) = true := by',
      '  simp only [rows, List.all_append, '+', '.join(p+'_certificate' for p in parts)+', Bool.and_self]',
      '#print axioms all_diagonal_integer_margins','end TernaryRichDiagonalCertificate','']
    (ROOT/'TernaryRichDiagonalCertificate.lean').write_text('\n'.join(lines))
    out=dict(status='COMPLETE_DIAGONAL_ENTRANCE_UNDER_INDEPENDENT_RECONSTRUCTION',u_min=4,u_max=32,
      r0='2u',contexts=contexts,context_count=len(contexts),integer_comparisons=checks,unique_margins=values,
      unique_count=len(values),chunks=len(parts),state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
      scope='EXACTcompletefinitepremiseONLYatdiagonalr=2u,4<=u<=32,ALLalpha1..r+floor(u/2),lastrepALLlargerbyFIRSTmodebound. Proposedunboundedr-closureNOTassertedfromfinitechecks.')
    (ROOT/'ternary_rich_diagonal_certificate_data.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('contexts','unique_margins')}),flush=True)
if __name__=='__main__':main()
