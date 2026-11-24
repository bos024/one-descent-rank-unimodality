"""COMPLETE finite proof inputs for max-capacity-four closure. Not random QA.
All unbounded parameters are reduced explicitly in the accompanying proof.
"""
from pathlib import Path
from collections import Counter
import sys,json,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_binary_first_defect_ordinary_tail import arm
from probe_mixed_binary_reference_ordinary_head import reference
from probe_small_three_unit_and_seed_bridges import ternary_reference,at

def main():
    ct=Counter();integers=set();sha=hashlib.sha256();contexts={}
    def record(kind,state,margins):
        assert min(margins,default=0)>=0,(kind,state,min(margins))
        contexts.setdefault(kind,[]).append(state)
        integers.update(margins);ct[kind+'_contexts']+=1;ct[kind+'_margins']+=len(margins)
        sha.update(json.dumps([kind,state,margins],separators=(',',':')).encode())
    # At w>=11 ALL small-s/r unresolved unit envelopes, not a sampled subset.
    for r in range(1,57):
        for s in range(1,18):
            if r+s<11:continue
            A=r+s+3;T=ternary_reference(s,A+4)
            margins=[T[n]**2-T[n-1]*T[n+1]+T[n-1] for n in range(A,A+3)]
            record('small_unit_reference',dict(r=r,s=s,read=T[A-1:A+4]),margins)
    # Only possible earlier ordinary entry outside T_s's proved head.
    for s in range(1,18):
        r=3*s-3
        if r<1:continue
        n=r+s+2;T=ternary_reference(s,n+2)
        record('first_boundary_unit',dict(r=r,s=s,n=n,read=T[n-1:n+2]),
            [T[n]**2-T[n-1]*T[n+1]+T[n-1]])
    h=[1,1,2,4,7,13,24];jet_clamp=[]
    for u in range(1,8):
        for alpha in range(1,8):
            f=arm(alpha,[2]*u)
            jets=[h[n]-at(f,n) for n in range(3,7)]
            assert all(x>=y for x,y in zip(jets,[1,2,5,11]))
            jet_clamp.append(dict(u=u,alpha=alpha,coefficients=[at(f,n) for n in range(7)],jets=jets))
    jets=sorted(set(tuple(row['jets']) for row in jet_clamp))
    # ALL remaining small-w startups: no unit envelope is presumed here.
    for r in range(1,10):
        for s in range(1,11-r):
            if (r,s)==(1,1):continue
            w=r+s;A=w+3;T=ternary_reference(s,A+4)
            for a,b,c,d in jets:
                losses=[0,a,w*a+b,w*(w+1)//2*a+w*b+c,
                    (w*(w+1)*(w+2)//6-r)*a+w*(w+1)//2*b+w*c+d]
                F=[T[A-1+j]-losses[j] for j in range(5)]
                margins=[F[j]**2-F[j-1]*F[j+1] for j in range(1,4)]
                record('small_full_seed_startup',dict(r=r,s=s,jets=[a,b,c,d],actual_reads=F),margins)
    for r in range(1,8):
        for s in range(1,9-r):
            if (r,s)==(1,1):continue
            V=[3]*r+[4]*s;W=sum(V);f=reference(V)
            record('small_four_terminal',dict(r=r,s=s,read=f[W-4:W+2]),
                [f[n]**2-f[n-1]*f[n+1] for n in range(W-3,W+1)])
    for r,s in [(r,0) for r in range(2,6)]+[(1,2)]:
        f=reference([3]*r+[4]*s);W=3*r+4*s;A=r+s+3
        record('small_reference_ordinary_base',dict(r=r,s=s,prefix=f[:W+2]),
            [f[n]**2-f[n-1]*f[n+1] for n in range(A,W+1)])
    # ALL padding representatives and ALL ordinary centres below the universal
    # first-D-mode bound; every larger padding agrees through the last read.
    for r,s,us in [(r,0,range(1,2*r+1)) for r in range(2,6)]+[(1,2,range(1,9))]:
        for u in us:
            w=u+r+s;L=(3*u+4*r+5*s)//2;alpha0=L-w+1;A=r+s+3
            for alpha in range(1,alpha0+1):
                f=arm(alpha,[2]*u+[3]*r+[4]*s)
                margins=[f[n]**2-f[n-1]*f[n+1] for n in range(A,L)]
                record('complete_actual_ordinary_base',dict(r=r,s=s,u=u,alpha=alpha,alpha0=alpha0,L=L,A=A,prefix=f[:L+1]),margins)
    values=sorted(integers)
    data=dict(status='COMPLETE_CAPACITY_FOUR_FINITE_PROOF_INPUTS',counts=dict(ct),contexts=contexts,
        binary_seed_clamp=jet_clamp,distinct_seed_jets=[list(x) for x in jets],
        integer_margins=values,state_sha256=sha.hexdigest(),
        scope='COMPLETE deterministic finite proof inputs only. r>=57/large-s/w>=11 analytic kernels reused. True special r1/s1 ordinaryLC FAILS, uses OLDtwo-nonbinaryFULLC instead.')
    (ROOT/'complete_capacity_four_base_data.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf8')
    lines=['import Mathlib','set_option maxRecDepth 4096','set_option maxHeartbeats 0','namespace CompleteCapacityFourBase','']
    chunks=[]
    for i in range(0,len(values),140):
        name='chunk_'+str(i//140);chunks.append(name)
        expr=' && '.join(f'decide ((0 : Int) ≤ {v})' for v in values[i:i+140])
        lines+=['private theorem '+name+' : ('+expr+') = true := by decide','']
    # The public theorem contains EVERY actual integer obligation and uses
    # every chunk; the statement never replaces the obligations by True.
    exprs=['('+' && '.join(f'decide ((0 : Int) ≤ {v})' for v in values[i:i+140])+')' for i in range(0,len(values),140)]
    lines+=['theorem complete_all_integer_bases : ('+' && '.join(exprs)+') = true := by',
        '  simp only ['+', '.join(chunks)+', Bool.and_self]',
        'end CompleteCapacityFourBase','#print axioms CompleteCapacityFourBase.complete_all_integer_bases']
    (ROOT/'CompleteCapacityFourBase.lean').write_text('\n'.join(lines)+'\n',encoding='utf8')
    print(json.dumps(dict(counts=dict(ct),distinct_integer_margins=len(values),chunks=len(chunks),distinct_seed_jets=len(jets),sha256=sha.hexdigest())),flush=True)
if __name__=='__main__':main()
