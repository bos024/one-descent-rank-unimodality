import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace AutomaticLateCInfiniteEdge

-- Coefficients of (1+z+z^2)^11 by disjoint choices of twos and ones.
def ciCoeff (n : ℕ) : ℕ :=
  (Finset.range 12).sum (fun a =>
    (Finset.range (12-a)).sum (fun b =>
      if 2*a+b=n then Nat.choose 11 a * Nat.choose (11-a) b else 0))

-- Coefficients of L * sum(k=0..7) z^k(1+z)^k, without polynomial-evaluation or native axioms.
def binaryCICoeff (n : ℕ) : ℕ :=
  (Finset.range 8).sum (fun k =>
    (Finset.range (k+1)).sum (fun j =>
      if k+j ≤ n then Nat.choose k j * ciCoeff (n-k-j) else 0))

theorem certified_infinite_tail_edge :
    binaryCICoeff 21 < binaryCICoeff 20 + 1 ∧
    binaryCICoeff 20 + 1 = 5109250 ∧
    binaryCICoeff 21 = 5076760 := by
  decide

#print axioms certified_infinite_tail_edge

end AutomaticLateCInfiniteEdge
