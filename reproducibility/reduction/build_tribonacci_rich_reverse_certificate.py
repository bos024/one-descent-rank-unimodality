"""ONE pure entrance, COMPLETE30 small-r rich contexts, and all real-cone corners."""
from pathlib import Path
from fractions import Fraction as F
from math import lcm
import json
from probe_tribonacci_quadratic_inverse import pc,add,sub,mul,power,sign,ZERO,ONE,A,B
ROOT=Path(__file__).resolve().parent
def reverse(E):
    J=[ZERO]*(len(E)-2);L=(0,1,0)
    for n in range(len(E)-3,-1,-1):
        v=(E[n+2],0,0)
        if n+1<len(J):v=sub(v,mul(A,J[n+1]))
        if n+2<len(J):v=sub(v,J[n+2])
        J[n]=mul(L,v)
    return J
def integral(v):
    v=tuple(map(F,v));d=lcm(*(x.denominator for x in v));return tuple(int(d*x) for x in v)
def lower_num(v,N,M):
    a,b,c=v;return a*M*M+b*(N if b>=0 else N+1)*M+c*(N*N if c>=0 else (N+1)**2)
def main():
    contexts=[];scalars=set();coeff_reads=0;minor_reads=0
    cases=[(u,r,'small_r_full_J') for u in range(4,9) for r in range(2*u,18)]+[(0,18,'pure_entrance_J_from2')]
    assert len(cases)==31
    for u,r,kind in cases:
        E=[1]
        for t in [2]*u+[3]*r:E=pc(E,[1]*t)
        J=reverse(E);start=2 if u==0 else 0;P=J[start:]
        ms=[sub(mul(P[n],P[n]),mul(P[n-1],P[n+1])) for n in range(1,len(P)-1)]
        assert all(sign(v)>0 for v in P+ms),(u,r)
        scalars.update(P+ms);coeff_reads+=len(P);minor_reads+=len(ms)
        contexts.append(dict(u=u,r=r,kind=kind,E=E,J=J,retained_start=start,retained_coefficients=P,minors=ms))
    allcorners={};corner_reads=0
    for name,file,key in [('reverse_extension','probe_reverse_tribonacci_bernstein_corners.json','18'),('whole_J_head','probe_reverse_tribonacci_head_payments.json','12')]:
        entries=json.loads((ROOT/file).read_text())['cases'][key];out={}
        for pname,entry in entries.items():
            assert entry['negative_count']==0 and entry['strict_constant_positive']
            rows=entry['complete_coefficient_data'];out[pname]=rows;corner_reads+=len(rows)
            for row in rows:
                v=integral(row['coefficient'])
                if v!=ZERO:scalars.add(v)
        allcorners[name]=out
    assert corner_reads==478
    def frac(q):return(F(q),F(0),F(0))
    S=(1,2,-1);P=mul(mul(A,A),B)
    assert P==(-3,0,1) and mul(S,B)==mul(A,A)
    controls={
      'b_minus_half':sub(B,frac(F(1,2))),
      'three_quarters_minus_a_square':sub(frac(F(3,4)),mul(A,A)),
      'three_fifths_minus_b':sub(frac(F(3,5)),B),
      'two_fifths_minus_a_square_b':sub(frac(F(2,5)),P),
      'sigma_minus_one':sub(S,ONE),'one_minus_b':sub(ONE,B),
      'pure_eighteen_norm_budget':sub(frac(F(1,64)),power(B,19)),
      'b_positive':B,'a_square_b_positive':P}
    for v in controls.values():scalars.add(integral(v))
    old=json.loads((ROOT/'tribonacci_inverse_complete_certificate_data.json').read_text());N=old['root_lower_numerator'];M=old['root_denominator']
    scalars=sorted(scalars);assert all(lower_num(v,N,M)>0 for v in scalars)
    chunks=[scalars[j:j+96] for j in range(0,len(scalars),96)]
    s='''import Mathlib
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
namespace TribonacciRichReverseCertificate
def lowerNumerator (v : ℤ × ℤ × ℤ) : ℤ :=
  let A := v.1
  let B := v.2.1
  let C := v.2.2
  let N : ℤ := '''+str(N)+'''
  let M : ℤ := '''+str(M)+'''
  A*M*M+B*(if 0 ≤ B then N else N+1)*M
    +C*(if 0 ≤ C then N*N else (N+1)*(N+1))
'''
    for i,chunk in enumerate(chunks):
        s+=f'def chunk{i} : List (ℤ × ℤ × ℤ) := [\n'+',\n'.join('  ('+', '.join(map(str,v))+')' for v in chunk)+']\n'
        s+=f'theorem pass{i} : chunk{i}.all (fun v => decide (0 < lowerNumerator v)) = true := by decide\n'
    s+='theorem complete_reverse_scalar_certificate :\n  '+' &&\n  '.join(f'chunk{i}.all (fun v => decide (0 < lowerNumerator v))' for i in range(len(chunks)))+' = true := by\n  simp only ['+', '.join('pass'+str(i) for i in range(len(chunks)))+']\n  decide\n'
    s+='#print axioms complete_reverse_scalar_certificate\nend TribonacciRichReverseCertificate\n'
    (ROOT/'TribonacciRichReverseCertificate.lean').write_text(s,encoding='utf8')
    data=dict(status='COMPLETE_RICH_REVERSE_DATA_NOT_YET_REGISTERED',contexts=contexts,base_coefficients=coeff_reads,base_minors=minor_reads,
      complete_corner_data=allcorners,Bernstein_coefficients=corner_reads,root_obligations={k:list(map(str,v)) for k,v in controls.items()},
      root_lower_numerator=N,root_denominator=M,positive_field_triples=scalars,chunks=len(chunks))
    (ROOT/'tribonacci_rich_reverse_certificate_data.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(dict(contexts=len(contexts),base_coefficients=coeff_reads,base_minors=minor_reads,Bernstein_coefficients=corner_reads,
      positive_field_triples=len(scalars),chunks=len(chunks))),flush=True)
if __name__=='__main__':main()
