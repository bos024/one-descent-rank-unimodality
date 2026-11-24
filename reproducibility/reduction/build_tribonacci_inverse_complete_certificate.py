"""Complete small entrance + exact Bernstein field coefficient certificate."""
from pathlib import Path
from math import lcm
from fractions import Fraction as F
import json
from probe_tribonacci_quadratic_inverse import pc,inverse,sub,mul,sign,ZERO
ROOT=Path(__file__).resolve().parent
def integral(v):
    q=tuple(F(x) for x in v);den=lcm(*(x.denominator for x in q));return tuple(int(den*x) for x in q)
def lower_num(v,N,M):
    A,B,C=v
    return A*M*M+B*(N if B>=0 else N+1)*M+C*(N*N if C>=0 else (N+1)**2)
def main():
    contexts=[];coefficients=set();zero_margins=0;prefix_reads=0;minor_reads=0
    for w in range(1,19):
        for u in range(w+1):
            r=w-u
            if (u,r)==(0,2):continue
            E=[1]
            for t in [2]*u+[3]*r:E=pc(E,[1]*t)
            f=inverse(E);kept=f[:-2]
            assert all(sign(v)>0 for v in kept)
            ms=[sub(mul(kept[n],kept[n]),mul(kept[n-1],kept[n+1])) for n in range(1,len(kept)-1)]
            assert all(sign(v)>=0 for v in ms),(u,r)
            coefficients.update(v for v in kept+ms if v!=ZERO);zero_margins+=ms.count(ZERO)
            prefix_reads+=len(kept);minor_reads+=len(ms)
            contexts.append(dict(u=u,r=r,E=E,prefix=kept,minors=ms))
    assert len(contexts)==188
    source=json.loads((ROOT/'probe_tribonacci_inverse_bernstein_corners.json').read_text())
    cases=source['cases']['18_1/4'];corners={};corner_reads=0
    for name,entry in cases.items():
        assert entry['negative_count']==0 and entry['strict_constant_positive']
        data=entry['complete_coefficient_data'];corner_reads+=len(data);corners[name]=data
        for row in data:
            v=integral([F(x) for x in row['coefficient']])
            if v!=ZERO:coefficients.add(v)
    M=10**50;lo=M;hi=2*M
    while hi-lo>1:
        n=(lo+hi)//2;p=n**3-n*n*M-n*M*M-M**3
        if p<0:lo=n
        else:hi=n
    N=lo;coefficients=sorted(coefficients)
    assert all(lower_num(v,N,M)>0 for v in coefficients)
    chunks=[coefficients[i:i+96] for i in range(0,len(coefficients),96)]
    text='''import Mathlib
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
namespace TribonacciInverseCompleteCertificate
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
        text+=f'def chunk{i} : List (ℤ × ℤ × ℤ) := [\n'
        text+=',\n'.join('  ('+', '.join(map(str,v))+')' for v in chunk)+']\n'
        text+=f'theorem pass{i} : chunk{i}.all (fun v => decide (0 < lowerNumerator v)) = true := by decide\n'
    text+='theorem all_positive_scalar_bounds :\n  '+' &&\n  '.join(f'chunk{i}.all (fun v => decide (0 < lowerNumerator v))' for i in range(len(chunks)))+' = true := by\n  simp only ['+', '.join('pass'+str(i) for i in range(len(chunks)))+']\n  decide\n'
    text+='\ntheorem exact_integer_cubic_root_bounds :\n  let n : ℤ := '+str(N)+'\n  let m : ℤ := '+str(M)+'\n  n^3-n^2*m-n*m^2-m^3 < 0 ∧ 0 < (n+1)^3-(n+1)^2*m-(n+1)*m^2-m^3 := by norm_num\n'
    text+='\n#print axioms all_positive_scalar_bounds\n#print axioms exact_integer_cubic_root_bounds\nend TribonacciInverseCompleteCertificate\n'
    (ROOT/'TribonacciInverseCompleteCertificate.lean').write_text(text,encoding='utf8')
    out=dict(status='COMPLETE_FINITE_ENTRANCE_AND_BERNSTEIN_DATA_NOT_YET_REGISTERED',complete_contexts=contexts,
      zero_minor_count=zero_margins,prefix_reads=prefix_reads,minor_reads=minor_reads,complete_corner_data=corners,
      corner_coefficient_count=corner_reads,positive_field_triples=coefficients,chunks=len(chunks),root_lower_numerator=N,root_denominator=M)
    (ROOT/'tribonacci_inverse_complete_certificate_data.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['complete_contexts','complete_corner_data','positive_field_triples']}),flush=True)
if __name__=='__main__':main()
