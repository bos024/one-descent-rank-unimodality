import Mathlib

set_option maxHeartbeats 0
namespace UniversalPrefixCWindowTransfer

theorem adaptive_prefix_budget {ι : Type*} (s : Finset ι)
    (d G : ι → ℝ) (dN GN base slack : ℝ)
    (hbase : dN ≤ (base-slack)*GN)
    (hp : ∀ i ∈ s, dN*G i ≤ d i*GN) :
    dN*(1+∑ i ∈ s,G i) ≤ (base-slack+∑ i ∈ s,d i)*GN := by
  have hh := Finset.sum_le_sum hp
  rw [← Finset.mul_sum,← Finset.sum_mul] at hh
  nlinarith

theorem adaptive_untruncated_payment (A U D d E C G : ℝ)
    (hbudget : D*C ≤ (A-E)*G) (hE : E=U-d)
    (hd : 0 ≤ d) (hCG : G ≤ C) :
    0 ≤ (A-U)*G-(D-d)*C := by
  have hh := mul_nonneg hd (sub_nonneg.mpr hCG)
  rw [hE] at hbudget
  nlinarith

theorem delayed_increment_comparison (E A : ℕ → ℝ) (N : ℕ)
    (h0 : A 0 ≤ E 0)
    (hstep : ∀ i < N, A (i+1)-A i ≤ E (i+1)-E i) :
    ∀ n, n ≤ N → A n ≤ E n := by
  intro n
  induction n with
  | zero => intro _;exact h0
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := hstep n (by omega)
    linarith

theorem dyadic_leading_prefix (n : ℕ) :
    1+∑ i ∈ Finset.range n,(2:ℝ)^i=(2:ℝ)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,pow_succ];linarith

theorem seed_loss_identity (L S T A D E : ℝ)
    (hL : L=T-D) (hS : S=T-A) (hE : E=A-D) : L-S=E := by
  rw [hL,hS,hE]
  ring

theorem seed_loss_budget (L S E m b C : ℝ)
    (hLS : L-S=E) (hE : m ≤ E) (hb : 0 ≤ b) (hC : C=b) :
    b*(m+S) ≤ L*C := by
  have hh : 0 ≤ b*(E-m) := mul_nonneg hb (sub_nonneg.mpr hE)
  rw [hC]
  nlinarith

theorem window_minor_loss_identity (N delta m Q S L b bs : ℝ)
    (hN : N=m*(Q-1)-S) (hd : delta=m*(b-bs)-L) :
    N*(b-bs)-delta*Q=L*Q-(m+S)*(b-bs) := by
  rw [hN,hd]
  ring

theorem window_payment_identity (L C Q b bs S : ℝ) (hQ : Q=C-bs+1) :
    C*(L*Q-(b-bs)*S)=Q*(L*C-b*S)+S*(bs*(C-b)+b) := by
  rw [hQ]
  ring

theorem window_prefix_payment (L C Q b bs S : ℝ)
    (hC : 0 < C) (hQ : Q=C-bs+1) (hQpos : 0 ≤ Q)
    (hb : 0 ≤ b) (hbs : 0 ≤ bs) (hS : 0 ≤ S)
    (hmass : b ≤ C) (hprefix : b*S ≤ L*C) :
    0 ≤ L*Q-(b-bs)*S := by
  have h1 : 0 ≤ Q*(L*C-b*S) := mul_nonneg hQpos (sub_nonneg.mpr hprefix)
  have h2 : 0 ≤ S*(bs*(C-b)+b) :=
    mul_nonneg hS (add_nonneg (mul_nonneg hbs (sub_nonneg.mpr hmass)) hb)
  have hid := window_payment_identity L C Q b bs S hQ
  have hp : 0 ≤ C*(L*Q-(b-bs)*S) := by rw [hid];linarith
  by_contra hn
  have hh := mul_neg_of_pos_of_neg hC (lt_of_not_ge hn)
  linarith

theorem binary_two_zeros_force_zero (w : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ w n) (h0 : w 0=0) (h1 : w 1=0)
    (hrec : ∀ n, w (n+2) ≤ w (n+1)+w n) : ∀ n,w n=0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact h0
    | succ m =>
      cases m with
      | zero => exact h1
      | succ k =>
        have ha := ih k (by omega)
        have hb := ih (k+1) (by omega)
        have hh := hrec k
        have hp := hpos (k+2)
        rw [ha,hb,add_zero] at hh
        exact le_antisymm hh hp

theorem small_three_seed (x y : ℝ) (hx : x ≤ 3) (hy : y ≤ 2*x-1) :
    y ≤ x+2 := by linarith

theorem small_four_shift_four_seed (d a b c : ℝ)
    (hd : d ≤ 3) (ha : a ≤ 2*d) (hb : b ≤ 2*a-1) (hc : c ≤ 2*b-2) :
    c ≤ d+a+b := by linarith

theorem small_four_shift_three_seed (d a b c : ℤ)
    (hd : 2 ≤ d ∧ d ≤ 3)
    (ha : a ≤ 2*d) (hb : b ≤ 2*a-1) (hc : c ≤ 2*b-2) :
    15*c ≤ (12+d)*(d+a+b) := by
  have hlo := hd.1
  have hhi := hd.2
  interval_cases d <;> nlinarith

theorem universal_seed_in_range (n t s k r : ℕ)
    (hn : n=t+s) (ht : k ≤ t+1) (hr : r ≤ s) : k+r-1 ≤ n := by omega

theorem remaining_window_conditions (n t r k : ℕ)
    (hprefix : t+max 4 (k-1) < n) (huntruncated : t+r ≤ n) :
    k ≤ n-t ∧ r ≤ n-t ∧ t+5 ≤ n := by omega

#print axioms adaptive_prefix_budget
#print axioms adaptive_untruncated_payment
#print axioms delayed_increment_comparison
#print axioms dyadic_leading_prefix
#print axioms seed_loss_identity
#print axioms seed_loss_budget
#print axioms window_minor_loss_identity
#print axioms window_payment_identity
#print axioms window_prefix_payment
#print axioms binary_two_zeros_force_zero
#print axioms small_three_seed
#print axioms small_four_shift_four_seed
#print axioms small_four_shift_three_seed
#print axioms universal_seed_in_range
#print axioms remaining_window_conditions
end UniversalPrefixCWindowTransfer
