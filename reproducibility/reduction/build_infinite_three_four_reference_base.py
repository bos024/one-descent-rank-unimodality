"""Build the COMPLETE finite entrance for s=1..22, not a sampled parameter test."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
def main():
    rows=[];values=[];boundaries=[]
    for s in range(1,23):
        N=4*s+1;h=[1]
        for n in range(1,N+1):h.append(sum(h[max(0,n-3):n]))
        f=h
        for _ in range(s):f=[1]+[sum(f[max(0,n-4):n]) for n in range(1,N+1)]
        minors=[f[n]**2-f[n-1]*f[n+1] for n in range(s+4,4*s-1)]
        assert min(minors,default=0)>=0
        rows.append(dict(s=s,first=s+4,last=4*s-2,F=f,minors=minors));values+=minors
        if s<=2:
            G=[];v=0
            for x in f:v+=x;G.append(v)
            N=4*s;k=N-3
            margin=(f[N-1]-f[N-2])*G[k]-(f[N]-f[N-1])*G[k-1]
            assert margin>=0;boundaries.append(margin)
    assert len(values)==651
    chunks=[values[i:i+150] for i in range(0,len(values),150)]
    text=['import Mathlib','set_option maxRecDepth 8192','set_option maxHeartbeats 3000000','namespace InfiniteThreeFourReferenceBase']
    for i,c in enumerate(chunks):
        text += [f'def chunk{i} : List ℤ := '+str(c),
          f'theorem checked{i} : chunk{i}.all (fun z => decide (0≤z))=true := by decide']
    text += ['def boundaryAndGrowth : List ℤ := '+str(boundaries+[1,0,3]),
      'theorem checkedBoundaryAndGrowth : boundaryAndGrowth.all (fun z => decide (0≤z))=true := by decide',
      'theorem complete_651_ordinary_head_base_minors : '+ ' ∧ '.join(f'chunk{i}.all (fun z => decide (0≤z))=true' for i in range(len(chunks)))+' ∧ boundaryAndGrowth.all (fun z => decide (0≤z))=true := by',
      '  exact ⟨checked0,checked1,checked2,checked3,checked4,checkedBoundaryAndGrowth⟩',
      '#print axioms complete_651_ordinary_head_base_minors','end InfiniteThreeFourReferenceBase']
    (ROOT/'InfiniteThreeFourReferenceBase.lean').write_text('\n'.join(text)+'\n')
    data=dict(status='COMPLETE_ENTRANCE_BUILT_NOT_YET_REGISTERED',contexts=rows,total_minors=len(values),integer_chunks=len(chunks),one_unit_cumulative_boundaries=boundaries,growth_seeds=[1,0,3])
    (ROOT/'infinite_three_four_reference_base_data.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(dict(contexts=len(rows),minors=len(values),chunks=len(chunks))),flush=True)
if __name__=='__main__':main()
