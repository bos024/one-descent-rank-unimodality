"""Emit a kernel-decide certificate for all 53 independently rebuilt exclusions."""
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parent


def main():
    producer=json.loads((ROOT/'probe_low_kappa_triangular_boundaries.json').read_text())
    independent=json.loads((ROOT/'verify_low_kappa_triangular_boundaries.json').read_text())
    assert producer['complete'] and independent['status']=='PASS_COMPLETE_INDEPENDENT_LOW_KAPPA_BOUNDARY_RECONSTRUCTION'
    assert producer['reachable_state_sha256']==independent['reachable_state_sha256']
    rows=producer['rejected_boundary_profiles']
    assert len(rows)==53
    header=r'''import Mathlib

/- Complete finite rejection of the 53 low-budget boundary jets. The full
jet grammar closure/coverage is independently rebuilt and proved in the
written TC assembly, not encoded end to end in this finite certificate. -/
set_option maxHeartbeats 0
set_option maxRecDepth 16384

namespace LowKappaBoundaryCertificate

def coeff (p : List ℕ) (n : ℕ) : ℕ := p[n]?.getD 0

def appendPrefix (p : List ℕ) (t : ℕ) : List ℕ :=
  1::((List.range (p.length-1)).map fun k =>
    ((List.range (min t (k+1))).map fun j => coeff p (k-j)).sum)

def derivative (p : List ℕ) (i : ℕ) : ℕ :=
  if 2 ≤ i then coeff p i-coeff p (i-1) else 0

def hasDropThrough (p : List ℕ) (n : ℕ) : Bool :=
  (List.range (n+1)).any fun i =>
    if 3 ≤ i then decide (derivative p i < derivative p (i-1)) else false

def rowCheck (row : List ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  let (p,t,kap,delta,n) := row
  let q := appendPrefix p t
  let kn := min (kap+1) (t+1)
  let dn := 2*coeff q (kn-1)-coeff q kn
  let B := max 1 (dn*(dn+1)/2-1)
  let value : ℤ := 3*(coeff q (n-1) : ℤ)-(coeff q n : ℤ)-2*(coeff q (n-2) : ℤ)
  decide (2*coeff p (kap-1)-coeff p kap=delta) &&
  decide (value<(B:ℤ)) &&
  (hasDropThrough p (n-1) || hasDropThrough q n)

def rows : List (List ℕ × ℕ × ℕ × ℕ × ℕ) := [
'''
    lines=[]
    for row in rows:
        vals=','.join(map(str,row['old_prefix']))
        lines.append(f"  ([{vals}],{row['t']},{row['kap']},{row['delta']},{row['n']})")
    footer=r''']

theorem all_53_low_budget_boundaries_have_a_prior_strict_fall :
    rows.length=53 ∧ rows.all rowCheck=true := by decide

#print axioms all_53_low_budget_boundaries_have_a_prior_strict_fall

end LowKappaBoundaryCertificate
'''
    target=ROOT/'LowKappaBoundaryCertificate.lean'
    target.write_text(header+',\n'.join(lines)+'\n'+footer,encoding='utf8')
    print(json.dumps(dict(status='GENERATED_EXACT_53_ROW_CERTIFICATE',rows=len(rows),file=target.name)),flush=True)


if __name__=='__main__':main()
