import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace CICountWedgeLateC

theorem source_wedge_gives_growth (w delta j prev cur : ℝ)
    (hw : 4*delta-5 ≤ w) (hj : 0 < j) (hji : j ≤ delta-1)
    (hp : 0 ≤ prev) (hg : (w-j+1)*prev ≤ j*cur) :
    3*prev ≤ cur := by
  have h1 := mul_nonneg (show 0 ≤ w+1-4*j by linarith only [hw,hji]) hp
  have hh : 0 ≤ j*(cur-3*prev) := by nlinarith only [h1,hg]
  have h := (mul_nonneg_iff_of_pos_left hj).mp hh
  linarith only [h]

theorem growth_sum_step (S prev cur : ℝ) (hs : 2*S ≤ 3*prev) (hg : 3*prev ≤ cur) :
    2*(S+cur) ≤ 3*cur := by linarith only [hs,hg]

theorem finite_loss_prefix_sum (l : ℕ → ℝ) (P : ℕ)
    (hl : ∀ i, i ≤ P → 0 ≤ l i)
    (hg : ∀ i, i < P → 3*l i ≤ l (i+1)) :
    ∀ n, n ≤ P → 2*(∑ i ∈ Finset.range (n+1), l i) ≤ 3*l n := by
  intro n
  induction n with
  | zero =>
    intro hn
    simp only [Nat.zero_add,Finset.sum_range_one]
    linarith only [hl 0 hn]
  | succ n ih =>
    intro hn
    have hnp : n ≤ P := by omega
    have hlt : n < P := by omega
    have hprev := ih hnp
    have hstep := hg n hlt
    rw [show n+1+1=(n+1)+1 by omega,Finset.sum_range_succ]
    exact growth_sum_step _ _ _ hprev hstep

theorem dyadic_ternary_all_distances : ∀ n : ℕ,
    (3:ℝ)*2^(n+1) ≤ 2*3^(n+1) := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : 0 ≤ (3:ℝ)^(n+1) := by positivity
    calc
      3*2^(n+1+1)=2*(3*2^(n+1)) := by rw [pow_succ]; ring
      _ ≤ 2*(2*3^(n+1)) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ ≤ 2*3^(n+1+1) := by
        have hpow : (3:ℝ)^(n+1+1)=3^(n+1)*3 := pow_succ 3 (n+1)
        rw [hpow]
        nlinarith only [hp]

theorem reference_CDF_growth_step (Fprev Fcur Gprevprev Gprev : ℝ)
    (hF : Fcur ≤ 2*Fprev) (hG : Gprev=Gprevprev+Fprev)
    (hp : Fprev ≤ Gprevprev) :
    Fcur ≤ Gprev ∧ Gprev+Fcur ≤ 2*Gprev := by
  constructor <;> linarith only [hF,hG,hp]

theorem strict_entry_gap (p x y b c lam : ℝ)
    (hp : p ≤ 2) (hx : b < x) (hb : 0 < b)
    (hgap : 0 < p*x-y) (hc : 3*b ≤ c)
    (hdef : lam*(x-b)=y-c) :
    lam < p ∧ b < (p-lam)*x := by
  have h1 := mul_nonneg (show 0 ≤ 2-p by linarith only [hp]) (le_of_lt hb)
  have hprod : 0 < (p-lam)*(x-b) := by nlinarith only [hgap,h1,hc,hb,hdef]
  have hden : 0 < x-b := by linarith only [hx]
  have hpl : 0 < p-lam := (mul_pos_iff_of_pos_right hden).mp hprod
  have hl2 : lam < 2 := by linarith only [hpl,hp]
  have h2 := mul_pos (show 0 < 2-lam by linarith only [hl2]) hb
  constructor
  · linarith only [hpl]
  · nlinarith only [hgap,hdef,hc,h2]

theorem double_cumulative_source_bound (T prev S lam : ℝ)
    (hl : 1 ≤ lam) (hp : 0 ≤ prev) (hT : T=prev+S) :
    T-lam*prev ≤ S := by
  have h := mul_nonneg (show 0 ≤ lam-1 by linarith only [hl]) hp
  nlinarith only [hT,h]

theorem dyadic_reference_resource (x U V r : ℝ)
    (hx : 2 ≤ x) (hUV : U=2*V) (hbound : x-1 ≤ V*r) :
    x ≤ U*r := by
  have heq := congrArg (fun z : ℝ => z*r) hUV
  nlinarith only [hx,hbound,heq]

theorem dyadic_source_payment (U V b s : ℝ)
    (hs : 0 ≤ s) (hUV : 3*U ≤ 2*V) (hsource : 2*V*s ≤ 3*b) :
    U*s ≤ b := by
  have h := mul_nonneg (show 0 ≤ 2*V-3*U by linarith only [hUV]) hs
  nlinarith only [h,hsource]

theorem prefix_read_paid (p lam x b U r cur source s : ℝ)
    (_hx : 0 < x) (hU : 0 < U) (hgap : 0 < p-lam)
    (hentry : b < (p-lam)*x) (hr : x ≤ U*r)
    (hcur : p*r ≤ cur) (hsource : source ≤ s) (hs : U*s ≤ b) :
    0 < cur-lam*r-source := by
  have h1 := mul_nonneg (le_of_lt hgap) (show 0 ≤ U*r-x by linarith only [hr])
  have h2 := mul_nonneg (le_of_lt hU) (show 0 ≤ cur-p*r by linarith only [hcur])
  have h3 := mul_nonneg (le_of_lt hU) (show 0 ≤ s-source by linarith only [hsource])
  have hh : 0 < U*(cur-lam*r-source) := by nlinarith only [h1,h2,h3,hentry,hs]
  exact (mul_pos_iff_of_pos_left hU).mp hh

theorem last_prefix_read_paid (p lam x b r cur source : ℝ)
    (hgap : 0 < p-lam) (hentry : b < (p-lam)*x)
    (hr : 3*x/2 ≤ r) (hcur : p*r ≤ cur) (hs : source ≤ 3*b/2) :
    0 < cur-lam*r-source := by
  have h1 := mul_nonneg (le_of_lt hgap) (show 0 ≤ r-3*x/2 by linarith only [hr])
  nlinarith only [h1,hentry,hcur,hs]

#print axioms source_wedge_gives_growth
#print axioms growth_sum_step
#print axioms finite_loss_prefix_sum
#print axioms dyadic_ternary_all_distances
#print axioms reference_CDF_growth_step
#print axioms strict_entry_gap
#print axioms double_cumulative_source_bound
#print axioms dyadic_reference_resource
#print axioms dyadic_source_payment
#print axioms prefix_read_paid
#print axioms last_prefix_read_paid
end CICountWedgeLateC
