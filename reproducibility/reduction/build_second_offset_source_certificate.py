"""Build a COMPLETE kernel-checked six-jet closure graph for the low offset-two lemma."""
from pathlib import Path
from collections import deque
import json,struct,hashlib
from probe_low_kappa_triangular_boundaries import app,slopes

ROOT=Path(__file__).resolve().parent


def main():
    N=6
    queue=deque();seen=set();edges=bad=0
    for alpha in range(1,N+1):
        F=tuple(int(i<=alpha) for i in range(N+1))
        seen.add((F,1,2));queue.append((F,1,2))
    while queue:
        F,last,k=queue.popleft()
        if k>=3:
            value=3*F[k+1]-F[k+2]-2*F[k]
            if value<1:
                bad+=1
                D=slopes(F)
                assert any(D[i]<D[i-1] for i in range(3,k+3))
        for t in range(max(2,last),N+1):
            kn=min(k+1,t+1)
            if kn>4:continue
            edges+=1
            key=(app(F,t),t,kn)
            if key not in seen:seen.add(key);queue.append(key)
    projected=set()
    fmt=struct.Struct('<'+'H'*14)
    with (ROOT/'low_kappa_boundary_states.bin').open('rb') as stream:
        while row:=stream.read(fmt.size+2):
            F=fmt.unpack_from(row);last,k=row[-2:]
            if k<=4:projected.add((F[:7],min(last,6),k))
    assert projected==seen
    assert (len(seen),edges,bad)==(106,179,15)
    header=r'''import Mathlib

/- ALL 106 finite states, ALL base states and ALL retained transition
closure conditions are checked by the Lean kernel. Actual-arm clamping
and the unbounded generation induction are the written coverage proof. -/
set_option maxHeartbeats 0
set_option maxRecDepth 16384

namespace SecondOffsetSourceCertificate

abbrev State := List ℕ × ℕ × ℕ
def coeff (p : List ℕ) (n : ℕ) : ℕ := p[n]?.getD 0
def appendPrefix (p : List ℕ) (t : ℕ) : List ℕ :=
  1::((List.range (p.length-1)).map fun n =>
    ((List.range (min t (n+1))).map fun j => coeff p (n-j)).sum)
def derivative (p : List ℕ) (n : ℕ) : ℕ :=
  if 2 ≤ n then coeff p n-coeff p (n-1) else 0
def hasDrop (p : List ℕ) (n : ℕ) : Bool :=
  (List.range (n+1)).any fun i =>
    if 3 ≤ i then decide (derivative p i < derivative p (i-1)) else false

def states : List State := [
'''
    lines=[]
    for F,last,k in sorted(seen):
        lines.append('  (['+','.join(map(str,F))+f'],{last},{k})')
    footer=r''']

def baseCheck : Bool :=
  (List.range 6).all fun a =>
    states.contains (((List.range 7).map fun i => if i≤a+1 then 1 else 0),1,2)

def closureCheck : Bool :=
  states.all fun s =>
    let (p,last,k) := s
    (List.range 5).all fun j =>
      let t := j+2
      let kn := min (k+1) (t+1)
      if last≤t ∧ kn≤4 then states.contains (appendPrefix p t,t,kn) else true

def curvatureCheck : Bool :=
  states.all fun s =>
    let (p,_,k) := s
    if 3≤k then
      let value : ℤ := 3*(coeff p (k+1) : ℤ)-(coeff p (k+2) : ℤ)-2*(coeff p k : ℤ)
      decide (1≤value) || hasDrop p (k+2)
    else true

theorem complete_six_jet_closure_and_curvature_certificate :
    states.length=106 ∧ baseCheck=true ∧ closureCheck=true ∧ curvatureCheck=true := by decide

#print axioms complete_six_jet_closure_and_curvature_certificate

end SecondOffsetSourceCertificate
'''
    text=header+',\n'.join(lines)+'\n'+footer
    (ROOT/'SecondOffsetSourceCertificate.lean').write_text(text,encoding='utf8')
    out=dict(status='GENERATED_COMPLETE_SECOND_OFFSET_SIX_JET_CERTIFICATE',N=N,
             states=106,retained_edges=179,excluded_small_curvature_states=15,
             exact_projection_from_independent_13_jet_state_set=True,
             lean_sha256=hashlib.sha256((ROOT/'SecondOffsetSourceCertificate.lean').read_bytes()).hexdigest(),
             scope='Finite complete closure graph. After clean Lean verification, with written actual coverage this proves DeltaE_(kappa+2)>=1 for kappa3/4 whenever FIRSTDmode>=kappa+2. Original UI OPEN.')
    (ROOT/'second_offset_source_certificate_build.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
