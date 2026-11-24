"""Complete u=1..9, r=6 ordinary pre-first-D-mode entrance, all padding represented."""
from pathlib import Path
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
def main():
    st=time.monotonic();rows=[];values=set();count=0;sha=hashlib.sha256()
    for u in range(1,10):
        clamp=6+u//2;bound=(3*u+24)//2
        for alpha in range(1,clamp+1):
            F=arm_prefix(alpha,[2]*u+[3]*6,alpha+2*u+18+1);D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];L=D.index(max(D));assert L<=bound
            ms=[]
            for n in range(9,L):
                v=F[n]**2-F[n-1]*F[n+1];assert v>=0,(u,alpha,n,L);ms.append(v);values.add(v);count+=1
            row=dict(u=u,r=6,alpha=alpha,clamp=clamp,bound=bound,mode=L,F=F,D=D,ordinary_centres=list(range(9,L)),ordinary_minors=ms)
            rows.append(row);sha.update(str(row).encode())
    vals=sorted(values);parts=[];lines=['import Mathlib','set_option maxHeartbeats 0','set_option maxRecDepth 100000','namespace AllBinaryTernaryOrdinaryBase','']
    for i,j in enumerate(range(0,len(vals),200)):
        p='part'+str(i);parts.append(p);lines+=['def '+p+' : List ℤ := ['+', '.join(map(str,vals[j:j+200]))+']',
          'theorem '+p+'_certificate : '+p+'.all (fun z => decide (0 ≤ z)) = true := by decide','']
    lines+=['def rows : List ℤ := '+' ++ '.join(parts),
      'theorem complete_fixed_six_small_binary_ordinary_entrance : rows.all (fun z => decide (0 ≤ z)) = true := by',
      '  simp only [rows, List.all_append, '+', '.join(p+'_certificate' for p in parts)+', Bool.and_self]',
      '#print axioms complete_fixed_six_small_binary_ordinary_entrance','end AllBinaryTernaryOrdinaryBase','']
    (ROOT/'AllBinaryTernaryOrdinaryBase.lean').write_text('\n'.join(lines),encoding='utf8')
    out=dict(status='COMPLETE_SMALL_BINARY_FIXED_SIX_ORDINARY_ENTRANCE_UNDER_INDEPENDENT_AUDIT',contexts=rows,context_count=len(rows),comparisons=count,unique_margins=vals,unique_count=len(vals),chunks=len(parts),state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      coverage='EVERYu1..9,r6,EVERYalpha1..6+floor(u/2),EVERYordinarycentre9<=n<FIRSTDmode. ALLlargerpaddingrepresentedEXACTLYthroughmodebound;postDmodeordinaryLCautomaticbyOLDstructure. NewfiniteordinarypremiseONLY.')
    (ROOT/'all_binary_ternary_ordinary_base_data.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['contexts','unique_margins']}),flush=True)
if __name__=='__main__':main()
