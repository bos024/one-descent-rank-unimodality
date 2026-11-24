"""COMPLETE finite entrances: ordinary fours and exact proper-quotient cut predicates."""
from pathlib import Path
from collections import Counter
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_tribonacci_quadratic_inverse import ZERO,ONE,A,B,add,sub,mul,pc,sign
from build_tribonacci_rich_reverse_certificate import reverse,lower_num,integral

def prefix_append(F,t):
    out=[1];v=0
    for n in range(1,len(F)):
        v+=F[n-1]-(F[n-t-1] if n>t else 0);out.append(v)
    return out
def prepare(r,s,N):
    I=[1]*(N+1);E=[1]
    for t in [3]*r+[4]*s:
        I=prefix_append(I,t);new=[];v=0
        for n in range(len(E)+t-1):
            v+=(E[n] if n<len(E) else 0)-(E[n-t] if n>=t else 0);new.append(v)
        E=new
    CE=[];v=0
    for en in E:v+=en;CE.append(v)
    return I,E,CE
def finite(I,CE,alpha,w):
    return [v-(CE[min(n-alpha-w-1,len(CE)-1)] if n>=alpha+w+1 else 0) for n,v in enumerate(I)]
def sc(v,c):return tuple(c*x for x in v)

def write_integer_certificate(values):
    chunks=[values[i:i+180] for i in range(0,len(values),180)]
    text=['import Mathlib','set_option maxRecDepth 65536','set_option maxHeartbeats 5000000','namespace CompleteThreeFourOrdinaryBase']
    for i,chunk in enumerate(chunks):
        text += [f'def chunk{i} : List ℤ := '+str(chunk),
          f'theorem checked{i} : chunk{i}.all (fun z => decide (0 ≤ z))=true := by decide']
    text += ['theorem complete_all_integer_entrances : ('+' && '.join(f'chunk{i}.all (fun z => decide (0 ≤ z))' for i in range(len(chunks)))+')=true := by',
      '  simp only ['+', '.join(f'checked{i}' for i in range(len(chunks)))+']',
      '  decide','#print axioms complete_all_integer_entrances','end CompleteThreeFourOrdinaryBase']
    (ROOT/'CompleteThreeFourOrdinaryBase.lean').write_text('\n'.join(text)+'\n')
    return len(chunks)
def write_field_certificate(values,N,M):
    chunks=[values[i:i+96] for i in range(0,len(values),96)]
    text=['import Mathlib','set_option maxRecDepth 65536','set_option maxHeartbeats 6000000','namespace CompleteThreeFourRootBase',
      'def lowerNumerator (v : ℤ × ℤ × ℤ) : ℤ :=',
      '  let A := v.1','  let B := v.2.1','  let C := v.2.2',f'  let N : ℤ := {N}',f'  let M : ℤ := {M}',
      '  A*M*M+B*(if 0 ≤ B then N else N+1)*M+C*(if 0 ≤ C then N*N else (N+1)*(N+1))']
    for i,c in enumerate(chunks):
        text += [f'def chunk{i} : List (ℤ × ℤ × ℤ) := ['+', '.join(str(tuple(v)) for v in c)+']',
          f'theorem checked{i} : chunk{i}.all (fun v => decide (0 < lowerNumerator v))=true := by decide']
    text += ['theorem complete_all_algebraic_predicates : ('+' && '.join(f'chunk{i}.all (fun v => decide (0 < lowerNumerator v))' for i in range(len(chunks)))+')=true := by',
      '  simp only ['+', '.join(f'checked{i}' for i in range(len(chunks)))+']','  decide',
      '#print axioms complete_all_algebraic_predicates','end CompleteThreeFourRootBase']
    (ROOT/'CompleteThreeFourRootBase.lean').write_text('\n'.join(text)+'\n')
    return len(chunks)
def main():
    st=time.monotonic();ct=Counter();ints=set();fields=set();ordinary=[];three=[];reused=[];sha=hashlib.sha256()
    root=json.loads((SOURCE/'tribonacci_inverse_complete_certificate_data.json').read_text());N=root['root_lower_numerator'];M=root['root_denominator']
    h=[1]
    for n in range(1,54):h.append(sum(h[max(0,n-3):n]))
    def ordinary_case(r,s,kind):
        L=(4*r+5*s)//2;w=r+s;A0=s+(3 if r==1 else 4);alpha0=L-w+1
        I,E,CE=prepare(r,s,L)
        before=ct['complete_ordinary_minors']
        for alpha in range(1,alpha0+1):
            F=finite(I,CE,alpha,w)
            for n in range(A0,L):
                v=F[n]**2-F[n-1]*F[n+1];assert v>=0,(r,s,alpha,n);ints.add(v);ct['complete_ordinary_minors']+=1
            sha.update(str((r,s,alpha,F)).encode());ct['complete_ordinary_hosts']+=1
        ordinary.append(dict(r=r,s=s,kind=kind,L=L,A=A0,alpha_clamp=alpha0,minor_count=ct['complete_ordinary_minors']-before))
    bsum=add(ONE,add(A,B))
    for r in range(1,50):
        star=max(8,(r+4)//3);ordinary_case(r,star,'four_heredity_entrance')
        for s in range(1,star):
            if 3*r+4*s<=32 or(r>=32 and r>=3*s+8):reused.append((r,s));continue
            if r+2<=3*s:ordinary_case(r,s,'small_four_phase');continue
            I,E,CE=prepare(r,s,r+s+3);Q=reverse(E)
            R0=sub(ONE,Q[0]);R1=sub(sub((r+s,0,0),Q[1]),mul(A,Q[0]));Rs=add(R0,R1)
            assert all(sign(v)>0 for v in Q)
            ms=[sub(mul(Q[n],Q[n]),mul(Q[n-1],Q[n+1])) for n in range(1,len(Q)-1)]
            assert all(sign(v)>=0 for v in ms)
            V0=add(mul(bsum,Q[0]),Rs);V1=add(V0,mul(bsum,Q[1]));V2=add(V1,mul(bsum,Q[2]));seed=sub(mul(V1,V1),mul(V0,V2))
            assert sign(V0)>0 and sign(seed)>=0
            entry=(1-2**s*h[r+2],2**s*h[r+1],0);assert lower_num(entry,N,M)>0
            P=r+s+2;F1=finite(I,CE,1,r+s)
            mI=I[P]**2-I[P-1]*I[P+1];mF=F1[P]**2-F1[P-1]*F1[P+1];assert min(mI,mF)>=0
            ints.update([mI,mF]);assert r+s>=10
            rows=Q+ms+[V0,seed,entry]
            for v in rows:
                if v!=ZERO:fields.add(integral(v))
            three.append(dict(r=r,s=s,E=E,Q=Q,remainder=[R0,R1],V0_scaled=V0,Vseed_scaled=seed,entry=entry,
              infinite_padding_j0_minor=mI,alpha_one_j0_minor=mF))
            ct['complete_three_cut_pairs']+=1;ct['complete_Q_values']+=len(Q);ct['complete_Q_minors']+=len(ms)
    seeds=[]
    for r in range(1,6):
        for alpha in range(1,8):
            I,E,CE=prepare(r,0,7);F=finite(I,CE,alpha,r);hh=[1]
            for n in range(1,8):hh.append(sum(hh[max(0,n-4):n]))
            a0=3 if r==1 else 4;losses=[hh[n]-F[n] for n in range(a0,a0+4)]
            aa,bb,cc,dd=losses;budgets=[aa-1,bb-2*aa,cc-4*aa+1,dd-8*aa+3]
            assert all(v>=0 for v in budgets);ints.update(budgets)
            assert F[:a0]==hh[:a0] and losses[0]>=1
            seeds.append(dict(r=r,alpha=alpha,first=a0,losses=losses,budgets=budgets))
    iv=sorted(ints);fv=sorted(fields);assert all(lower_num(v,N,M)>0 for v in fv)
    ic=write_integer_certificate(iv);fc=write_field_certificate(fv,N,M)
    out=dict(status='COMPLETE_THREE_FOUR_BOUNDARY_BASES_BUILT_UNREGISTERED',counts=dict(ct),ordinary_contexts=ordinary,three_cut_contexts=three,
      reused_old_C_pairs=reused,startup_seed_contexts=seeds,integer_margins=iv,field_scalars=fv,integer_chunks=ic,field_chunks=fc,
      root_lower_numerator=N,root_denominator=M,ordinary_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st)
    (ROOT/'complete_three_four_boundary_data.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(counts=dict(ct),ordinary_contexts=len(ordinary),three_cut_contexts=len(three),reused_pairs=len(reused),startup_contexts=len(seeds),
      unique_integer=len(iv),unique_fields=len(fv),integer_chunks=ic,field_chunks=fc,seconds=out['seconds'])),flush=True)
if __name__=='__main__':main()
