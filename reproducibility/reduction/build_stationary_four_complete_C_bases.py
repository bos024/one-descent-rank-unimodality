"""Complete fixed-eight ordinary and golden-residual entrances, not parameter QA."""
from pathlib import Path
import sys,json,hashlib,time
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from verify_ternary_forward_inverse import qa,qm,qs,sub
def sc(v,k):return tuple(k*x for x in v)
def expr(v):return f'(({v[0]}:ℝ)+({v[1]}:ℝ)*q)'
def main():
    st=time.monotonic();rows=[];vals=set();comparisons=0
    for u in range(21):
        clamp=(u+24)//2;bound=(3*u+40)//2;A=10 if u==0 else 11
        for alpha in range(1,clamp+1):
            F=arm_prefix(alpha,[2]*u+[4]*8,alpha+2*u+32+1)
            D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];L=D.index(max(D));assert L<=bound
            centres=list(range(A,L));ms=[F[n]**2-F[n-1]*F[n+1] for n in centres];assert min(ms,default=0)>=0
            vals.update(ms);comparisons+=len(ms)
            rows.append(dict(u=u,alpha=alpha,r=8,clamp=clamp,bound=bound,A=A,L=L,F=F,D=D,centres=centres,minors=ms))
    assert len(rows)==352 and comparisons==8554
    values=sorted(vals);parts=[]
    lines=['import Mathlib','set_option maxHeartbeats 0','set_option maxRecDepth 100000','namespace StationaryFourOrdinaryBase','']
    for i,j in enumerate(range(0,len(values),200)):
        name='part'+str(i);parts.append(name)
        lines+=['def '+name+' : List ℤ := ['+', '.join(map(str,values[j:j+200]))+']',
          'theorem '+name+'_certificate : '+name+'.all (fun z => decide (0 ≤ z)) = true := by decide','']
    lines+=['def rows : List ℤ := '+' ++ '.join(parts),
      'theorem complete_fixed_eight_small_binary_ordinary_entrance : rows.all (fun z => decide (0 ≤ z)) = true := by',
      '  simp only [rows, List.all_append, '+', '.join(n+'_certificate' for n in parts)+', Bool.and_self]',
      '#print axioms complete_fixed_eight_small_binary_ordinary_entrance','end StationaryFourOrdinaryBase','']
    (ROOT/'StationaryFourOrdinaryBase.lean').write_text('\n'.join(lines),encoding='utf8')
    h=[1]
    for n in range(1,18):h.append(sum(h[max(0,n-4):n]))
    K=[(h[n]-(h[n-1] if n else 0),-(h[n-1] if n else 0)) for n in range(len(h))]
    field=[]
    def push(tag,v,strict=False):
        assert qs(v)>0 if strict else qs(v)>=0,(tag,v)
        field.append(dict(tag=tag,value=v,strict=strict))
    for n in range(2,9):
        m=h[n]**2-h[n-1]*h[n+1]
        push('hminor_minus_'+str(n),(h[n-1]-m,0));push('hminor_plus_'+str(n),(h[n-1]+m,0))
    for n in range(7,14):
        m=sub(qm(K[n],K[n]),qm(K[n-1],K[n+1]))
        push('Kminor_minus_'+str(n),sub(K[n-1],m));push('Kminor_plus_'+str(n),qa(K[n-1],m))
    for n in range(5,9):push('K_lower_growth_'+str(n),sub(sc(K[n+1],5),sc(K[n],9)),True)
    for n in range(6,10):push('K_upper_growth_'+str(n),sub(sc(K[n],2),K[n+1]),True)
    for n in range(2,6):push('K_positive_'+str(n),K[n],True)
    for n in range(1,5):
        push('h_lower_growth_'+str(n),(5*h[n+1]-9*h[n],0))
        push('h_upper_growth_'+str(n),(2*h[n-1]-h[n],0))
    # Positive numerator C8=1+(z3+z4)*sum_{j<8}S4^j, then inverse(1+qz).
    C=[1]+[0]*32;P=[1]
    for _ in range(8):
        for n,v in enumerate(P):C[n+3]+=v;C[n+4]+=v
        P=[0]+[sum(P[max(0,n-3):min(n+1,len(P))]) for n in range(len(P)+3)]
    H=[];v=(0,0)
    for c in C:v=sub((c,0),qm((0,1),v));H.append(v)
    for n in range(10,33):push('H8_positive_'+str(n),H[n],True)
    for n in range(11,32):push('H8_LC_'+str(n),sub(qm(H[n],H[n]),qm(H[n-1],H[n+1])))
    props=[f'0{ "<" if v["strict"] else "≤" }{expr(v["value"])}' for v in field]
    lean='''import Mathlib
set_option maxHeartbeats 3000000
namespace StationaryFourFieldBase
theorem exact_q_interval (q : ℝ) (hq : q^2+q=1) (hp : 0 ≤ q) :
    618033988749/1000000000000 ≤ q ∧ q ≤ 618033988750/1000000000000 := by
  constructor
  · by_contra! h
    have hs := mul_self_le_mul_self hp (le_of_lt h)
    nlinarith
  · by_contra! h
    have hs := mul_self_le_mul_self (show (0:ℝ) ≤ 618033988750/1000000000000 by norm_num) (le_of_lt h)
    nlinarith
theorem complete_quartic_majorant_and_fixed_eight_reference_entrance
    (q : ℝ) (hq : q^2+q=1) (hp : 0 ≤ q) :
    '''+' ∧\n    '.join(props)+''' := by
  have hi := exact_q_interval q hq hp
  refine ⟨'''+', '.join('?_ ' for _ in props).strip()+'''⟩ <;> nlinarith [hq,hi.1,hi.2]
#print axioms complete_quartic_majorant_and_fixed_eight_reference_entrance
end StationaryFourFieldBase
'''
    (ROOT/'StationaryFourFieldBase.lean').write_text(lean,encoding='utf8')
    out=dict(contexts=rows,context_count=len(rows),comparisons=comparisons,unique_margins=values,unique_count=len(values),chunks=len(parts),
      h=h,K=K,field_rows=field,C8=C,H8=H,field_scalar_count=len(field),seconds=time.monotonic()-st)
    (ROOT/'stationary_four_complete_C_base_data.json').write_text(json.dumps(out)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['contexts','unique_margins','field_rows','h','K','C8','H8']}),flush=True)
if __name__=='__main__':main()
