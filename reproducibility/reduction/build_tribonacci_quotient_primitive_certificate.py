"""Complete full-primitive base31 and every low-rank Bernstein coefficient."""
from pathlib import Path
from fractions import Fraction as F
from math import lcm
import json
from probe_tribonacci_quadratic_inverse import ZERO,sub,mul,sign
ROOT=Path(__file__).resolve().parent
def integral(v):
    v=tuple(map(F,v));d=lcm(*(x.denominator for x in v));return tuple(int(d*x) for x in v)
def lower(v,N,M):
    a,b,c=v;return a*M*M+b*(N if b>=0 else N+1)*M+c*(N*N if c>=0 else (N+1)**2)
def main():
    old=json.loads((ROOT/'tribonacci_rich_reverse_certificate_data.json').read_text());N=old['root_lower_numerator'];M=old['root_denominator']
    contexts=[];scalars=set();reads=0;coeffs=0
    for row in old['contexts']:
        J=list(map(tuple,row['J']));raw=[sub(v,J[n-1] if n else ZERO) for n,v in enumerate(J)]
        D=[v if sign(v)>0 else ZERO for v in raw]
        ms=[sub(mul(D[n],D[n]),mul(D[n-1],D[n+1])) for n in range(1,len(D)-1)]
        assert all(sign(v)>=0 for v in ms)
        for v in raw:
            if v!=ZERO:scalars.add(v if sign(v)>0 else tuple(-x for x in v))
        scalars.update(v for v in ms if v!=ZERO)
        contexts.append(dict(u=row['u'],r=row['r'],J=J,signed_primitive=raw,positive_primitive=D,minors=ms))
        reads+=len(ms);coeffs+=len(D)
    heads=json.loads((ROOT/'probe_tribonacci_quotient_primitive_head.json').read_text())['cases']['12'];corner={};ncoeff=0
    for name,entry in heads.items():
        assert entry['negative_count']==0 and entry['strict_constant_positive']
        rows=entry['complete_coefficient_data'];corner[name]=rows;ncoeff+=len(rows)
        for row in rows:
            v=integral(row['coefficient'])
            if v!=ZERO:scalars.add(v)
    assert len(contexts)==31 and reads==933 and ncoeff==235
    # A separate ACTUAL-arm obstruction to replacing this quotient by the WHOLE residual.
    dinf=[]
    for t in [2]*20+[3]*40:
        new=[0]*(len(dinf)+t) if dinf else [0]*(t-1)
        for j in range(t-1):new[j]+=1
        for n,v in enumerate(dinf):
            for j in range(1,t+1):new[n+j]+=v
        dinf=new
    residual=[(-v,dinf[n-1] if n else 0,0) for n,v in enumerate(dinf)]
    primitive=[sub(v,residual[n-1] if n else ZERO) for n,v in enumerate(residual)]
    triple=primitive[76:79];assert all(sign(v)>0 for v in triple)
    counter=sub(mul(triple[1],triple[1]),mul(triple[0],triple[2]));assert sign(counter)<0
    scalars.add(tuple(-x for x in counter))
    control=dict(u=20,r=40,alpha=160,shifted_centre=77,shifted_first_D_mode=dinf.index(max(dinf)),
      positive_residual_primitive_triple=triple,negative_minor=counter,
      scope='ACTUALfinitepaddingalpha160realizesentiredinfpositiveDsupport;countertotheWHOLElambda-residualpositiveprimitiveLC,NOToriginalUI/C/Jprimitive.')
    scalars=sorted(scalars);assert all(lower(v,N,M)>0 for v in scalars)
    chunks=[scalars[i:i+96] for i in range(0,len(scalars),96)]
    s='''import Mathlib
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
namespace TribonacciQuotientPrimitiveCertificate
def lowerNumerator (v : ℤ × ℤ × ℤ) : ℤ :=
  let A := v.1
  let B := v.2.1
  let C := v.2.2
  let N : ℤ := '''+str(N)+'''
  let M : ℤ := '''+str(M)+'''
  A*M*M+B*(if 0 ≤ B then N else N+1)*M
    +C*(if 0 ≤ C then N*N else (N+1)*(N+1))
'''
    for i,ch in enumerate(chunks):
        s+=f'def chunk{i} : List (ℤ × ℤ × ℤ) := [\n'+',\n'.join('  ('+', '.join(map(str,v))+')' for v in ch)+']\n'
        s+=f'theorem pass{i} : chunk{i}.all (fun v => decide (0 < lowerNumerator v)) = true := by decide\n'
    s+='theorem complete_positive_primitive_certificate :\n  '+' &&\n  '.join(f'chunk{i}.all (fun v => decide (0 < lowerNumerator v))' for i in range(len(chunks)))+' = true := by\n  simp only ['+', '.join('pass'+str(i) for i in range(len(chunks)))+']\n  decide\n'
    s+='#print axioms complete_positive_primitive_certificate\nend TribonacciQuotientPrimitiveCertificate\n'
    (ROOT/'TribonacciQuotientPrimitiveCertificate.lean').write_text(s,encoding='utf8')
    data=dict(status='COMPLETE_QUADRATIC_QUOTIENT_PRIMITIVE_DATA_NOT_REGISTERED',contexts=contexts,complete_primitive_coefficients=coeffs,
      complete_primitive_minors=reads,complete_head_data=corner,Bernstein_coefficients=ncoeff,root_lower_numerator=N,root_denominator=M,
      positive_field_triples=scalars,chunks=len(chunks),actual_residual_primitive_counter=control)
    (ROOT/'tribonacci_quotient_primitive_certificate_data.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(dict(contexts=len(contexts),primitive_coefficients=coeffs,primitive_minors=reads,Bernstein_coefficients=ncoeff,
      positive_field_triples=len(scalars),chunks=len(chunks))),flush=True)
if __name__=='__main__':main()
