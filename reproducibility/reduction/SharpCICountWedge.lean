import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000
namespace SharpCICountWedge

theorem interval_amplification_all_capacities (p : ℝ)
    (hp : 8/5 ≤ p) (hq : p^2=p+1) :
    ∀ k : ℕ, ((k:ℝ)+3)*(8/7)^(k+3) ≤ p^(k+4)-p := by
  have hp0 : 0 ≤ p := by linarith only [hp]
  have hp4 : p^4=3*p+2 := by
    calc
      p^4=(p^2)^2 := by ring
      _=(p+1)^2 := by rw [hq]
      _=3*p+2 := by nlinarith only [hq]
  intro k
  induction k with
  | zero => norm_num; rw [hp4]; linarith only [hp]
  | succ k ih =>
    have ht : 3 ≤ (k:ℝ)+3 := by have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k; linarith only [hk]
    have hc := mul_nonneg (show 0 ≤ p-8/5 by linarith only [hp])
      (show 0 ≤ (k:ℝ)+3 by positivity)
    have hcoef : (((k:ℝ)+3)+1)*(8/7) ≤ p*((k:ℝ)+3) := by
      nlinarith only [hc,ht]
    have hpow : 0 ≤ (8/7:ℝ)^(k+3) := by positivity
    have h1 := mul_nonneg (show 0 ≤ p*((k:ℝ)+3)-(((k:ℝ)+3)+1)*(8/7) by linarith only [hcoef]) hpow
    have h2 := mul_nonneg hp0 (show 0 ≤ p^(k+4)-p-((k:ℝ)+3)*(8/7)^(k+3) by linarith only [ih])
    have hrec : p^(k+5)-p=p*(p^(k+4)-p)+1 := by
      rw [show k+5=(k+4)+1 by omega,pow_succ]
      nlinarith only [hq]
    have hpowrec : (8/7:ℝ)^(k+4)=(8/7)^(k+3)*(8/7) := by
      rw [show k+4=(k+3)+1 by omega,pow_succ]
    rw [show k+1+3=k+4 by omega,show k+1+4=k+5 by omega,hrec,hpowrec]
    push_cast
    nlinarith only [h1,h2]

theorem fifteen_rank_amplification : (117/16:ℚ) ≤ (8/7)^15 := by norm_num

theorem reference_mass_budget (p s T P x : ℝ)
    (hp0 : 0 < p) (hp : p ≤ 13/8) (hs0 : 0 < s) (hs : s ≤ 9/4)
    (hT : 117/16 ≤ T) (hP : 0 ≤ P) (hbinet : P*T ≤ p*s*x) :
    2*P ≤ x := by
  have h1 := mul_nonneg (show 0 ≤ 13/8-p by linarith only [hp]) (le_of_lt hs0)
  have h2 : 2*p*s ≤ T := by nlinarith only [h1,hs,hT]
  have h3 := mul_nonneg hP (show 0 ≤ T-2*p*s by linarith only [h2])
  have hd : 0 < p*s := mul_pos hp0 hs0
  have hprod : p*s*(2*P) ≤ p*s*x := by nlinarith only [h3,hbinet]
  exact (mul_le_mul_iff_of_pos_left hd).mp hprod

theorem reference_ratio_eight_fifths (q t x y : ℝ)
    (hq0 : 0 ≤ q) (hq : q^2+q=1) (ht : t ≤ 34-55*q)
    (ht0 : 0 ≤ t) (hx : 0 < x)
    (hdef : y*(1+t)=x*(1+q-q*t)) : 8*x/5 ≤ y := by
  have h1 := mul_nonneg (show 0 ≤ q+8/5 by linarith only [hq0])
    (show 0 ≤ 34-55*q-t by linarith only [ht])
  have hg : 0 ≤ 1+q-q*t-(8/5)*(1+t) := by nlinarith only [h1,hq]
  have h2 := mul_nonneg (le_of_lt hx) hg
  have hp : 0 ≤ (1+t)*(y-8*x/5) := by nlinarith only [h2,hdef]
  have hh := (mul_nonneg_iff_of_pos_left (show 0 < 1+t by linarith only [ht0])).mp hp
  linarith only [hh]

theorem reference_cumulative_mass_resources (x y M : ℝ)
    (hx : 0 ≤ x) (hy : 8*x/5 ≤ y) (hM : M ≤ x/2) :
    2*x ≤ x+y-M ∧ 7*x/2 ≤ x+2*y-M := by constructor <;> linarith only [hx,hy,hM]

theorem sharp_wedge_geometry (w delta : ℝ)
    (hd : 5 ≤ delta) (hw : 13*delta ≤ 4*w+17) : 17 ≤ w+delta := by linarith only [hd,hw]

theorem sharp_wedge_source_growth (w delta j prev cur : ℝ)
    (hw : 13*delta ≤ 4*w+17) (hj : 0 < j) (hji : j ≤ delta-1)
    (hp : 0 ≤ prev) (hg : (w-j+1)*prev ≤ j*cur) :
    9*prev/4 ≤ cur := by
  have h1 := mul_nonneg (show 0 ≤ 4*w+4-13*j by linarith only [hw,hji]) hp
  have hh : 0 ≤ j*(4*cur-9*prev) := by nlinarith only [h1,hg]
  have h := (mul_nonneg_iff_of_pos_left hj).mp hh
  linarith only [h]

theorem doubling_loss_finite_sum (l : ℕ → ℝ) (P : ℕ)
    (hl : ∀ i, i ≤ P → 0 ≤ l i)
    (hg : ∀ i, i < P → 2*l i ≤ l (i+1)) :
    ∀ n, n ≤ P → (∑ i ∈ Finset.range (n+1), l i) ≤ 2*l n := by
  intro n
  induction n with
  | zero => intro hn; simp only [Nat.zero_add,Finset.sum_range_one]; linarith only [hl 0 hn]
  | succ n ih =>
    intro hn
    have hprev := ih (show n ≤ P by omega)
    have hstep := hg n (by omega)
    rw [show n+1+1=(n+1)+1 by omega,Finset.sum_range_succ]
    linarith only [hprev,hstep]

theorem sharp_entry_gap (p x y b c lam : ℝ)
    (hp : p ≤ 13/8) (hx : b < x) (hb : 0 < b)
    (hgap : 0 < p*x-y) (hc : 9*b/4 ≤ c)
    (hdef : lam*(x-b)=y-c) : lam < p ∧ 5*b/8 < (p-lam)*x := by
  have h1 := mul_nonneg (show 0 ≤ 13/8-p by linarith only [hp]) (le_of_lt hb)
  have hprod : 0 < (p-lam)*(x-b) := by nlinarith only [hgap,h1,hc,hb,hdef]
  have hpl : 0 < p-lam := (mul_pos_iff_of_pos_right (show 0 < x-b by linarith only [hx])).mp hprod
  have hl : lam < 13/8 := by linarith only [hpl,hp]
  have h2 := mul_pos (show 0 < 13/8-lam by linarith only [hl]) hb
  constructor
  · linarith only [hpl]
  · nlinarith only [hgap,hdef,hc,h2]

theorem sharp_interior_prefix_paid (p lam x b U r cur source : ℝ)
    (hb : 0 < b) (hU : 0 < U) (hg : 0 < p-lam)
    (he : 5*b/8 < (p-lam)*x) (hr : 4*x ≤ U*r)
    (hcur : p*r ≤ cur) (hs : U*source ≤ 2*b) :
    0 < cur-lam*r-source := by
  have h1 := mul_nonneg (le_of_lt hg) (show 0 ≤ U*r-4*x by linarith only [hr])
  have h2 := mul_nonneg (le_of_lt hU) (show 0 ≤ cur-p*r by linarith only [hcur])
  have hh : 0 < U*(cur-lam*r-source) := by nlinarith only [h1,h2,he,hs,hb]
  exact (mul_pos_iff_of_pos_left hU).mp hh

theorem sharp_last_prefix_paid (p lam x b r cur source : ℝ)
    (hb : 0 < b) (hg : 0 < p-lam) (he : 5*b/8 < (p-lam)*x)
    (hr : 7*x/2 ≤ r) (hcur : p*r ≤ cur) (hs : source ≤ 2*b) :
    0 < cur-lam*r-source := by
  have h1 := mul_nonneg (le_of_lt hg) (show 0 ≤ r-7*x/2 by linarith only [hr])
  nlinarith only [h1,he,hcur,hs,hb]

theorem sharp_ordinary_seed (x y a b c A : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) (hx : b ≤ x)
    (hy : 8*x/5 ≤ y) (hc : 9*b/4 ≤ c) :
    A+7*b^2/20 ≤ A-x*(a+2*b)+y*(a-b+c)+b^2+a*b-a*c := by
  have ht : 0 ≤ a-b+c := by linarith only [ha,hb,hc]
  have h1 := mul_nonneg (show 0 ≤ y-8*x/5 by linarith only [hy]) ht
  have hc0 : 0 ≤ (3/5)*a-(18/5)*b+(8/5)*c := by linarith only [ha,hc]
  have h2 := mul_nonneg (show 0 ≤ x-b by linarith only [hx]) hc0
  have h3 := mul_nonneg (show 0 ≤ c-9*b/4 by linarith only [hc])
    (show 0 ≤ 8*b/5-a by linarith only [hab,hb])
  have h4 := mul_nonneg (show 0 ≤ b-a by linarith only [hab]) (le_of_lt hb)
  nlinarith only [h1,h2,h3,h4]

#print axioms interval_amplification_all_capacities
#print axioms fifteen_rank_amplification
#print axioms reference_mass_budget
#print axioms reference_ratio_eight_fifths
#print axioms reference_cumulative_mass_resources
#print axioms sharp_wedge_geometry
#print axioms sharp_wedge_source_growth
#print axioms doubling_loss_finite_sum
#print axioms sharp_entry_gap
#print axioms sharp_interior_prefix_paid
#print axioms sharp_last_prefix_paid
#print axioms sharp_ordinary_seed
end SharpCICountWedge
