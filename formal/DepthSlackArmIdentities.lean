import Mathlib

namespace DepthSlackArmIdentities

variable {R : Type*} [CommRing R]

/-- The unshifted interval of length n, evaluated at x. -/
def interval (x : R) : ℕ → R
  | 0 => 0
  | n+1 => 1 + x * interval x n

def step (x : R) (n : ℕ) : R := x * interval x n

theorem interval_loss (x : R) (n : ℕ) :
    (1-x) * interval x n = 1-x^n := by
  induction n with
  | zero => simp [interval]
  | succ n ih =>
    simp only [interval, pow_succ]
    linear_combination x * ih

theorem step_loss (x : R) (n : ℕ) :
    step x n * (1-x) = x-x*x^n := by
  unfold step
  linear_combination x * interval_loss x n

/-- Sum of the products in all depth layers in outside-to-inside order. -/
def layers (x : R) : List ℕ → R
  | [] => 1
  | n :: ns => 1 + step x n * layers x ns

/-- The next-capacity shift at every depth, including the final capacity zero. -/
def nextLoss (x : R) : List ℕ → R
  | [] => 1
  | n :: ns => x^n + step x n * nextLoss x ns

theorem all_depth_births (x : R) (caps : List ℕ) :
    (1-2*x)*layers x caps = 1-x-x*nextLoss x caps := by
  induction caps with
  | nil => simp [layers, nextLoss]; ring
  | cons n ns ih =>
    simp only [layers, nextLoss]
    linear_combination step x n * ih + step_loss x n

/-- Here d represents an actual part d+2, and a represents a+1 leading ones. -/
def actual (x : R) (a : ℕ) : List ℕ → R
  | [] => interval x (a+2)
  | d :: ds => 1 + step x (d+2) * actual x a ds

def deepest (x : R) : List ℕ → R
  | [] => 1
  | d :: ds => step x (d+2) * deepest x ds

def proper (x : R) : List ℕ → R
  | [] => 0
  | d :: ds => 1 + step x (d+2) * proper x ds

def upperSlope (x : R) : List ℕ → R
  | [] => 0
  | d :: ds => interval x (d+1) + step x (d+2) * upperSlope x ds

def thresholdLoss (x : R) : List ℕ → R
  | [] => 0
  | d :: ds => x^(d+1) + step x (d+2) * thresholdLoss x ds

theorem deepest_split (x : R) (a : ℕ) (ds : List ℕ) :
    actual x a ds = proper x ds + deepest x ds * interval x (a+2) := by
  induction ds with
  | nil => simp [actual, proper, deepest]
  | cons d ds ih =>
    simp only [actual, proper, deepest]
    rw [ih]
    ring

theorem signed_finite_padding (x : R) (a : ℕ) (ds : List ℕ) :
    (1-x) * actual x a ds =
      1 + x^2 * upperSlope x ds - x^(a+2) * deepest x ds := by
  induction ds with
  | nil => simpa [actual, upperSlope, deepest] using interval_loss x (a+2)
  | cons d ds ih =>
    simp only [actual, upperSlope, deepest]
    have h : step x (d+2) = x+x^2*interval x (d+1) := by
      change x*(1+x*interval x (d+1)) = x+x^2*interval x (d+1)
      ring
    linear_combination step x (d+2) * ih + h

theorem threshold_complement (x : R) (ds : List ℕ) :
    (1-x)*upperSlope x ds = proper x ds-thresholdLoss x ds := by
  induction ds with
  | nil => simp [upperSlope, proper, thresholdLoss]
  | cons d ds ih =>
    simp only [upperSlope, proper, thresholdLoss]
    linear_combination step x (d+2) * ih + interval_loss x (d+1)

theorem proper_is_reference_host (x : R) (ds : List ℕ) (last : ℕ) :
    proper x (ds ++ [last]) = layers x (ds.map (fun d => d+2)) := by
  induction ds with
  | nil => simp [proper,layers]
  | cons d ds ih =>
    simp only [List.cons_append, List.map_cons, proper, layers, ih]

end DepthSlackArmIdentities

#print axioms DepthSlackArmIdentities.interval_loss
#print axioms DepthSlackArmIdentities.step_loss
#print axioms DepthSlackArmIdentities.all_depth_births
#print axioms DepthSlackArmIdentities.deepest_split
#print axioms DepthSlackArmIdentities.signed_finite_padding
#print axioms DepthSlackArmIdentities.threshold_complement
#print axioms DepthSlackArmIdentities.proper_is_reference_host
