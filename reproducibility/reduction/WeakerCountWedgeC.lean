import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000

namespace WeakerCountWedgeC

theorem golden_rational_two_sided (q : ℝ) (hq0 : 0≤q) (hq : q≤5/8)
    (heq : q^2+q=1) : 8/13≤q ∧ 8/5≤q+1 := by
  have hm : q*(q+1)=1 := by nlinarith
  have hh := mul_nonneg hq0 (show 0≤13/8-(q+1) by linarith)
  constructor <;> nlinarith

theorem CI_prefix_mass_bound (E : ℕ → ℝ) (K : ℕ)
    (hE : ∀ i, i≤K → 0≤E i)
    (hg : ∀ i, i<K → (9/4)*E i≤E (i+1)) :
    ∀ n, n≤K → (∑ i ∈ Finset.range (n+1), E i)≤(9/5)*E n := by
  intro n
  induction n with
  | zero => intro hn; simp only [Nat.zero_add,Finset.sum_range_one]; nlinarith [hE 0 hn]
  | succ n ih =>
      intro hn
      have hs := ih (show n≤K by omega)
      have hh := hg n (by omega)
      rw [show n+1+1=(n+1)+1 by omega,Finset.sum_range_succ]
      nlinarith

theorem ordinary_positive_kernel_upper (q E S f : ℝ)
    (hq0 : 0≤q) (hq : q≤5/8) (heq : q^2+q=1)
    (hE : 0≤E) (hS : S≤(9/5)*E) (hf : f≤E) :
    q*S+q^2*f≤(3/2)*E := by
  have h1 := mul_nonneg hq0 (show 0≤(9/5)*E-S by linarith)
  have h2 := mul_nonneg (sq_nonneg q) (show 0≤E-f by linarith)
  have h3 := mul_nonneg (show 0≤5/8-q by linarith) hE
  have he := congrArg (fun x : ℝ => x*E) heq
  nlinarith

theorem padding_one_ordinary_gap_upper (q E f R : ℝ)
    (heq : q^2+q=1) (hf : f≤E) (hR : 0≤R) :
    (q+1)*E+q^2*f-R≤2*E := by
  have h1 := mul_nonneg (sq_nonneg q) (show 0≤E-f by linarith)
  have he := congrArg (fun x : ℝ => x*E) heq
  nlinarith

theorem finite_padding_next_correction (q prev cur : ℝ)
    (hq : q≤5/8) (hp : 0≤prev) (hg : (15/8)*prev≤cur) :
    (1/4)*prev≤cur-(q+1)*prev := by
  nlinarith [mul_nonneg (show 0≤5/8-q by linarith) hp]

theorem next_actual_golden_gap (q C0 f fprev Ecur Enext extra : ℝ)
    (hq0 : 0≤q) (hq : q≤5/8) (hc : 0≤C0) (he : 0≤Ecur)
    (hfprev : fprev≤Ecur) (hf : f=Enext-q*fprev)
    (hg : (15/8)*Ecur≤Enext) (hextra : 0≤extra) :
    (5/4)*Ecur≤C0+f+extra := by
  have h1 := mul_nonneg hq0 (show 0≤Ecur-fprev by linarith)
  have h2 := mul_nonneg (show 0≤5/8-q by linarith) he
  nlinarith

theorem seed_budgets_padding_one (p q B C g ecur eprev : ℝ)
    (hp : 8/5≤p) (hq : 8/13≤q) (hB : 0<B) (hC : (9/4)*B≤C)
    (hg : (3/2)*C≤g) (hecur : ecur≤2*C) (heprev : eprev≤2*B) :
    ecur<p*g ∧ eprev<q*g := by
  have hg0 : 0<g := by nlinarith
  have h1 := mul_nonneg (show 0≤p-8/5 by linarith) (le_of_lt hg0)
  have h2 := mul_nonneg (show 0≤q-8/13 by linarith) (le_of_lt hg0)
  constructor <;> nlinarith

theorem seed_budgets_padding_two (p q B C g ecur eprev : ℝ)
    (hp : 8/5≤p) (hq : 8/13≤q) (hB : 0<B) (hC : (9/4)*B≤C)
    (hg : (5/4)*C+(5/8)*B≤g) (hecur : ecur≤(35/18)*C)
    (heprev : eprev≤(35/18)*B) : ecur<p*g ∧ eprev<q*g := by
  have hg0 : 0<g := by nlinarith
  have h1 := mul_nonneg (show 0≤p-8/5 by linarith) (le_of_lt hg0)
  have h2 := mul_nonneg (show 0≤q-8/13 by linarith) (le_of_lt hg0)
  constructor <;> nlinarith

theorem seed_budgets_padding_at_least_three (p q B C g ecur eprev : ℝ)
    (hp : 8/5≤p) (hq : 8/13≤q) (hB : 0<B) (hC : (9/4)*B≤C)
    (hg : (5/4)*C≤g) (hecur : ecur≤(35/18)*C)
    (heprev : eprev≤(275/162)*B) : ecur<p*g ∧ eprev<q*g := by
  have hg0 : 0<g := by nlinarith
  have h1 := mul_nonneg (show 0≤p-8/5 by linarith) (le_of_lt hg0)
  have h2 := mul_nonneg (show 0≤q-8/13 by linarith) (le_of_lt hg0)
  constructor <;> nlinarith

theorem preceding_ordinary_ratio_resource (q a Fprev Fprevprev dprev : ℝ)
    (hF : (q+1)*a≤Fprev) (hd : dprev≤a) (hdef : Fprevprev=Fprev-dprev) :
    q*a≤Fprevprev := by nlinarith

theorem ordinary_seed_transfer (a H c g e : ℝ) (ha : 0<a) (hg : 0<g)
    (hH : c*a≤H) (he : e<c*g) : 0<H*g-a*e := by
  have h1 := mul_nonneg (show 0≤H-c*a by linarith) (le_of_lt hg)
  have h2 := mul_pos ha (show 0<c*g-e by linarith)
  have hid : H*g-a*e=(H-c*a)*g+a*(c*g-e) := by ring
  rw [hid]
  exact add_pos_of_nonneg_of_pos h1 h2

theorem complete_missing_prefix_reads (lam G0 G1 G2 G3 F0 F1 F2 : ℝ)
    (h0 : G1=G0+F0) (h1 : G2=G1+F1) (h2 : G3=G2+F2)
    (hG : lam*G0≤G1) (hF1 : lam*F0≤F1) (hF2 : lam*F1≤F2) :
    lam*G1≤G2 ∧ lam*G2≤G3 := by
  have hid1 : G2-lam*G1=(G1-lam*G0)+(F1-lam*F0) := by rw [h1,h0]; ring
  have hg2 : lam*G1≤G2 := by nlinarith
  have hid2 : G3-lam*G2=(G2-lam*G1)+(F2-lam*F1) := by rw [h2,h1]; ring
  constructor <;> nlinarith

theorem weaker_wedge_geometry (u h r w delta n : ℤ)
    (_hu : 0≤u) (hr : 2*r≤h) (hw : w=u+r) (hd : delta=h-u)
    (hn : n=delta-2) (hdelta : 5≤delta) (hweight : 33≤w+delta)
    (hcone : 13*delta≤4*w+30) :
    h≤3*u+2 ∧ 3≤n ∧ 13*n≤4*w+4 ∧ 15*(n+1)≤8*(w-n) := by
  by_cases hn8 : 8≤n <;> omega

theorem nine_gap_new_wedge_or_small (w delta : ℤ) (hd : delta≤9)
    (hn : 4*w+30<13*delta) : w+delta≤30 := by omega

theorem reference_entry_cumulative_resource (x y M : ℝ)
    (hy : (8/5)*x≤y) (hM : 5*M≤2*x) : (6/5)*x≤y-M+1 := by linarith

#print axioms golden_rational_two_sided
#print axioms CI_prefix_mass_bound
#print axioms ordinary_positive_kernel_upper
#print axioms padding_one_ordinary_gap_upper
#print axioms finite_padding_next_correction
#print axioms next_actual_golden_gap
#print axioms seed_budgets_padding_one
#print axioms seed_budgets_padding_two
#print axioms seed_budgets_padding_at_least_three
#print axioms preceding_ordinary_ratio_resource
#print axioms ordinary_seed_transfer
#print axioms complete_missing_prefix_reads
#print axioms weaker_wedge_geometry
#print axioms nine_gap_new_wedge_or_small
#print axioms reference_entry_cumulative_resource

end WeakerCountWedgeC
