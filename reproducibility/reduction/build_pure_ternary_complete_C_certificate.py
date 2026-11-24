"""Complete small pure-three entrance, with literal all-rank/all-shift margins."""
from pathlib import Path
import sys,json,hashlib,time
from itertools import accumulate
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix

def main():
    start=time.monotonic();rows=[];unique=set();count=0;sha=hashlib.sha256()
    for r in range(11,18):
        for alpha in range(1,r+1):
            F=arm_prefix(alpha,[3]*r,alpha+3*r+1)
            D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];L=D.index(max(D));G=list(accumulate(F));assert L<=2*r
            margins=[]
            for N in range(4,2*r+1):
                for k in range(1,N-2):
                    m=G[k]*D[N-1]-G[k-1]*D[N];assert m>=0,(r,alpha,N,k)
                    margins.append(m);unique.add(m);count+=1
            row=dict(r=r,alpha=alpha,mode=L,F=F,D=D,literal_C_margins=margins)
            rows.append(row);sha.update(str(row).encode())
    vals=sorted(unique);parts=[];lines=['import Mathlib','set_option maxHeartbeats 0','set_option maxRecDepth 100000','namespace PureTernaryCompleteCCertificate','']
    for i,startidx in enumerate(range(0,len(vals),300)):
        p='part'+str(i);parts.append(p)
        lines+=['def '+p+' : List ℤ := ['+', '.join(map(str,vals[startidx:startidx+300]))+']',
          'theorem '+p+'_certificate : '+p+'.all (fun z => decide (0 ≤ z)) = true := by decide','']
    lines+=['def rows : List ℤ := '+' ++ '.join(parts),
      'theorem complete_small_pure_ternary_integer_entrance : rows.all (fun z => decide (0 ≤ z)) = true := by',
      '  simp only [rows, List.all_append, '+', '.join(p+'_certificate' for p in parts)+', Bool.and_self]',
      '#print axioms complete_small_pure_ternary_integer_entrance','end PureTernaryCompleteCCertificate','']
    (ROOT/'PureTernaryCompleteCCertificate.lean').write_text('\n'.join(lines),encoding='utf8')
    out=dict(status='COMPLETE_98_PURE_THREE_ACTUAL_ENTRANCE_UNDER_INDEPENDENT_AUDIT',
      contexts=rows,context_count=len(rows),integer_comparisons=count,unique_margins=vals,unique_count=len(vals),chunks=len(parts),
      state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
      exact_coverage='EVERY11<=r<=17,EVERY1<=alpha<=r,EVERY4<=N<=2r,EVERY1<=k<=N-3. ALLliteralCproducts;NOsampledentrance. GenericfirstDmode<=2r andalpharepresentativeproofrequiredforunboundedfamily.')
    (ROOT/'pure_ternary_complete_C_certificate_data.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['contexts','unique_margins']}),flush=True)
if __name__=='__main__':main()
