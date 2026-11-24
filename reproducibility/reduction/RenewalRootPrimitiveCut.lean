import Mathlib
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace RenewalRootPrimitiveCut

def ramp (q : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => q*ramp q n+((n:ℝ)+2)

def rootsum (q : ℝ) : ℕ → ℝ
  | 0 => q
  | n+1 => q*(1+rootsum q n)

theorem exact_notch_minor_identity (V R q : ℝ) :
    (V-2-q*R)^2-(V-R)*(V-3-2*q-q^2*R)
      =4+V*(2*q-1)+R*(V*(1-q)^2+2*q-3) := by ring

theorem whole_large_width_notch_payment (V R q L : ℝ)
    (hq0 : 1/2 ≤ q) (hq1 : q ≤ 2/3) (hR : 0 ≤ R)
    (hL : 5 ≤ L) (hV : V*(1-q)=L) :
    4 ≤ (V-2-q*R)^2-(V-R)*(V-3-2*q-q^2*R) := by
  have hv0 : 0 ≤ V := by
    by_contra! h
    have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_lt h) (show 0 ≤ 1-q by linarith)
    linarith
  have hid : V*(1-q)^2+2*q-3=(L-2)*(1-q)-1 := by
    linear_combination (1-q)*hV
  have hc : 0 ≤ V*(1-q)^2+2*q-3 := by
    rw [hid]
    have hp := mul_nonneg (show 0 ≤ L-5 by linarith) (show 0 ≤ 1-q by linarith)
    nlinarith
  have h1 := mul_nonneg hv0 (show 0 ≤ 2*q-1 by linarith)
  have h2 := mul_nonneg hR hc
  rw [exact_notch_minor_identity]
  linarith

theorem all_small_width_notch_minors (L : ℕ) (hl : 2 ≤ L) (hu : L ≤ 4) :
    (L:ℝ)*max 0 ((L:ℝ)-3) ≤ ((L:ℝ)-2)^2 := by
  interval_cases L <;> norm_num

theorem whole_unbounded_ramp_fixed_point (q : ℝ) (M : ℕ)
    (hroot : rootsum q M=1) : (1-q)*ramp q M=(M:ℝ) := by
  have hid : ∀ n : ℕ,(1-q)*ramp q n=((n:ℝ)+1)-rootsum q n := by
    intro n
    induction n with
    | zero => simp [ramp,rootsum]
    | succ n ih =>
        simp only [ramp,rootsum,Nat.cast_add,Nat.cast_one]
        linear_combination q*ih
  have h := hid M
  rw [hroot] at h
  linarith

theorem all_renewal_root_bounds (q : ℝ) (M : ℕ)
    (hq : 0 < q) (hM : 1 ≤ M) (hroot : rootsum q M=1) :
    1/2 ≤ q ∧ q ≤ 2/3 := by
  have hn : ∀ n : ℕ,0 ≤ rootsum q n := by
    intro n
    induction n with
    | zero => simp [rootsum];positivity
    | succ n ih => simp only [rootsum];positivity
  have hl : ∀ n : ℕ,q ≤ rootsum q n := by
    intro n
    cases n with
    | zero => simp [rootsum]
    | succ n => simp only [rootsum];nlinarith [mul_nonneg (le_of_lt hq) (hn n)]
  have h2 : q+q^2 ≤ 1 := by
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : M ≠ 0)
    rw [hn,rootsum] at hroot
    nlinarith [mul_nonneg (le_of_lt hq) (show 0 ≤ rootsum q n-q by linarith [hl n])]
  have hgeo : ∀ n : ℕ,(1-q)*rootsum q n=q-q^(n+2) := by
    intro n
    induction n with
    | zero => simp [rootsum];ring
    | succ n ih =>
        simp only [rootsum,pow_succ]
        simp only [pow_succ] at ih
        linear_combination q*ih
  have hg := hgeo M
  rw [hroot] at hg
  have hp := pow_pos hq (M+2)
  constructor
  · linarith
  · by_contra! h
    have hs := mul_self_le_mul_self (show (0:ℝ) ≤ 2/3 by norm_num) (le_of_lt h)
    nlinarith

theorem complete_interval_product_spike_factor {R : Type*} [CommRing R]
    (z IP IL zP zL : R) (hL : (1-z)*IL=1-zL) :
    (1-z)*(IP*IL+zP)=(IP+zP)-z*zP-zL*IP := by
  linear_combination IP*hL

theorem whole_cut_three_read_band (t ell n M : ℕ)
    (ht : 2 ≤ t) (hn : ell+t ≤ n) (hM : n<M) :
    ell+t-2 < n-1 ∧ n+1 ≤ M ∧
      t-1 ≤ n-1-ell ∧ t-1 ≤ n-ell ∧ t-1 ≤ n+1-ell := by omega

theorem complete_geometric_tail_minor_propagation (q A B C g h k : ℝ)
    (hB : B=q*A+g) (hC : C=q*B+h) :
    g*(C*h-B*k)=q*h*(B*g-A*h)+B*(h^2-g*k) := by
  linear_combination -h*h*hB+g*h*hC

theorem whole_decreasing_ramp_first_minor (V q : ℝ) :
    (V-1)^2-V*(V-2-q)=1+q*V := by ring

#print axioms exact_notch_minor_identity
#print axioms whole_large_width_notch_payment
#print axioms all_small_width_notch_minors
#print axioms whole_unbounded_ramp_fixed_point
#print axioms all_renewal_root_bounds
#print axioms complete_interval_product_spike_factor
#print axioms whole_cut_three_read_band
#print axioms complete_geometric_tail_minor_propagation
#print axioms whole_decreasing_ramp_first_minor

end RenewalRootPrimitiveCut
