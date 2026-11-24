import Mathlib

/- Kernel-checked finite inputs for midpoint_terminal_bridge.tex.
   The parameter reduction and the combinatorial layer argument are written
   proofs; this file does not claim to formalize the whole theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace MidpointTerminalFinite

def coef (p : List ℕ) (n : ℕ) : ℕ := p[n]?.getD 0

def initial (alpha : ℕ) : List ℕ :=
  (List.range 13).map fun i => if i ≤ alpha then 1 else 0

def step (p : List ℕ) (t : ℕ) : List ℕ :=
  (List.range 13).map fun n => if n = 0 then 1 else
    ((List.range (min t n)).map fun j => coef p (n-j-1)).sum

def arm (alpha : ℕ) (U : List ℕ) : List ℕ := U.foldl step (initial alpha)

def productCoef (p q : List ℕ) (n : ℕ) : ℕ :=
  ((List.range (n+1)).map fun i => coef p i * coef q (n-i)).sum

def parts : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, total => if total = 0 then [[]] else []
  | k+1, lo, total =>
    ((List.range (total/(k+1)+1)).filter fun t => lo ≤ t).flatMap fun t =>
      (parts k t (total-t)).map fun rest => t::rest

def profiles (r weight : ℕ) : List (ℕ × List ℕ) :=
  (List.range weight).flatMap fun a =>
    (parts (r-1) 2 (weight-a-1)).map fun U => (a+1,U)

def largeFactors (alpha : ℕ) (U : List ℕ) : ℕ :=
  (if 2 ≤ alpha then 1 else 0) + (U.filter fun t => 3 ≤ t).length

def profileData (r weight : ℕ) : List (List ℕ × ℕ) :=
  (profiles r weight).map fun p => (arm p.1 p.2, largeFactors p.1 p.2)

def lowFamily (r : ℕ) : Bool :=
  ((List.range (r/2+1)).filter fun rx => 2 ≤ rx).all fun rx =>
    ((List.range 21).filter fun a => 3 ≤ a).all fun a =>
      let left := profileData rx a
      let right := profileData (r-rx) (23-a)
      left.all fun A => right.all fun B =>
        decide (r*(r-2)+2*(A.2+B.2) ≤ productCoef A.1 B.1 11)

def binaryTernary : ℕ → List (List ℕ)
  | 0 => [[]]
  | k+1 => ((binaryTernary k).map fun U => 2::U) ++ [List.replicate (k+1) 3]

def clippedEight : Bool :=
  [2,3,4].all fun rx => [1,2].all fun alpha => [1,2].all fun beta =>
    (binaryTernary (rx-1)).all fun U =>
      (binaryTernary (7-rx)).all fun V =>
        let h := largeFactors alpha U + largeFactors beta V
        let D := alpha+beta+U.sum+V.sum
        decide (8*6+2*h+1 ≤ productCoef (arm alpha U) (arm beta V) (D/2))

theorem low_four : lowFamily 4 = true := by decide
theorem low_five : lowFamily 5 = true := by decide
theorem low_six : lowFamily 6 = true := by decide
theorem low_seven : lowFamily 7 = true := by decide
theorem eight : clippedEight = true := by decide

#print axioms low_four
#print axioms low_five
#print axioms low_six
#print axioms low_seven
#print axioms eight

end MidpointTerminalFinite
