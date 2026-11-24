import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000

namespace CountWedgeBoundaryPositive

theorem reference_amplification_all_large :
    ∀ k : ℕ, (585/64:ℝ) ≤ (8/7)^(k+17) := by
  intro k
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [show k+1+17=(k+17)+1 by omega,pow_succ]
      nlinarith [pow_nonneg (show (0:ℝ)≤8/7 by norm_num) (k+17)]

theorem reference_mass_two_fifths (P M x : ℝ) (hM : M≤P)
    (hscale : (585/64)*P≤(117/32)*x) : 5*M≤2*x := by linarith

lemma prod_sum_nonempty (V : List ℕ) (hne : V≠[])
    (ht : ∀ t ∈ V, 3≤t) : V.sum≤V.prod ∧ 3≤V.prod := by
  induction V with
  | nil => contradiction
  | cons t V ih =>
      have ht0 := ht t (by simp)
      by_cases hempty : V=[]
      · subst V; simpa using And.intro (le_refl t) ht0
      · obtain ⟨hs,hp⟩ := ih hempty (by intro a ha; exact ht a (by simp [ha]))
        have h1 := Nat.mul_le_mul_right V.prod ht0
        have h2 := Nat.mul_le_mul_left t hp
        simp only [List.sum_cons,List.prod_cons]
        constructor <;> nlinarith

theorem interval_product_sum_margin (V : List ℕ) (hlen : 2≤V.length)
    (ht : ∀ t ∈ V, 3≤t) : V.sum+3≤V.prod := by
  cases V with
  | nil => simp at hlen
  | cons t V =>
      have hne : V≠[] := by intro h; subst V; simp at hlen
      obtain ⟨hs,hp⟩ := prod_sum_nonempty V hne (by intro a ha; exact ht a (by simp [ha]))
      have ht0 := ht t (by simp)
      have h1 := Nat.mul_le_mul_right V.prod ht0
      have h2 := Nat.mul_le_mul_left t hp
      simp only [List.sum_cons,List.prod_cons]
      nlinarith

theorem reference_previous_read_budget (q P x y M b1 : ℝ)
    (hq : q≤5/8) (hP : 20≤P) (hx : 2*P≤x)
    (hy : y≤(q+1)*x) (hM : 5*M≤2*x) (hb1 : 0≤b1) :
    40≤x ∧ y-x+1≤(13/20)*x ∧ (3/5)*x≤x-M+b1 := by
  have h40 : 40≤x := by linarith
  have hmul := mul_nonneg (show 0≤5/8-q by linarith) (show 0≤x by linarith)
  constructor
  · exact h40
  constructor <;> nlinarith

theorem finite_padding_positive_correction (q prev cur : ℝ)
    (hq : q≤5/8) (hp : 0≤prev) (hg : (9/4)*prev≤cur) :
    (5/8)*prev≤cur-(q+1)*prev := by
  nlinarith [mul_nonneg (show 0≤5/8-q by linarith) hp]

theorem uniform_actual_golden_gap (q C0 f fprev Eprev Ecur extra : ℝ)
    (hq0 : 0≤q) (hq : q≤5/8) (hc : 0≤C0) (he : 0≤Eprev)
    (hfprev : fprev≤Eprev) (hf : f=Ecur-q*fprev)
    (hg : (9/4)*Eprev≤Ecur) (hextra : 0≤extra) :
    (13/8)*Eprev≤C0+f+extra := by
  have h1 := mul_nonneg hq0 (show 0≤Eprev-fprev by linarith)
  have h2 := mul_nonneg (show 0≤5/8-q by linarith) he
  nlinarith

theorem renewal_response_prefix_bound (E H : ℕ → ℝ) (K : ℕ)
    (hE : ∀ i, i≤K → 0≤E i)
    (hg : ∀ i, i<K → (9/4)*E i≤E (i+1))
    (h0 : H 0=E 0) (h1 : H 1=E 1+E 0)
    (hr : ∀ i, i+2≤K → H (i+2)=E (i+2)+H (i+1)+H i) :
    ∀ n, n≤K → H n≤(81/29)*E n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      cases n with
      | zero => rw [h0]; nlinarith [hE 0 hn]
      | succ k =>
          cases k with
          | zero => rw [h1]; nlinarith [hg 0 (by omega),hE 1 hn]
          | succ m =>
              change H (m+2)≤(81/29)*E (m+2)
              have b0 := ih m (by omega) (by omega)
              have b1 := ih (m+1) (by omega) (by omega)
              have g0 := hg m (by omega)
              have g1 := hg (m+1) (by omega)
              have hh := hr m (by omega)
              nlinarith

theorem loss_cumulative_prefix_bound (E l : ℕ → ℝ) (K : ℕ)
    (hE : ∀ i, i≤K → 0≤E i)
    (hg : ∀ i, i<K → (9/4)*E i≤E (i+1))
    (hl : ∀ i, i≤K → l i≤(110/29)*E i) :
    ∀ n, n≤K → (∑ i ∈ Finset.range (n+1), l i)≤(198/29)*E n := by
  intro n
  induction n with
  | zero =>
      intro hn
      simp only [Nat.zero_add,Finset.sum_range_one]
      nlinarith [hE 0 hn,hl 0 hn]
  | succ n ih =>
      intro hn
      have hs := ih (show n≤K by omega)
      have hh := hg n (by omega)
      have hc := hl (n+1) hn
      rw [show n+1+1=(n+1)+1 by omega,Finset.sum_range_succ]
      nlinarith

theorem geometric_interval_lower (E : ℕ → ℝ) (K j : ℕ)
    (hg : ∀ i, i<K → (9/4)*E i≤E (i+1)) :
    ∀ m, j+m≤K → (9/4:ℝ)^m*E j≤E (j+m) := by
  intro m
  induction m with
  | zero => intro hm; simp
  | succ m ih =>
      intro hm
      have hp := ih (show j+m≤K by omega)
      have hs := hg (j+m) (by omega)
      rw [pow_succ]
      have hh := mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤9/4 by norm_num)
      have hi : j+(m+1)=j+m+1 := by omega
      rw [hi]
      nlinarith

theorem all_distance_boundary_constant (m : ℕ) :
    (243/32:ℝ)≤(243/32)*(9/8)^m := by
  have hp : (1:ℝ)≤(9/8)^m := by
    induction m with
    | zero => norm_num
    | succ m ih => rw [pow_succ]; nlinarith
  nlinarith

theorem increasing_pair_source_bound (a b Tcur Tprev S E : ℝ)
    (ha : 0≤a) (hab : a≤b) (ht : 0≤Tprev)
    (hS : Tcur-Tprev=S) (hE : S≤(198/29)*E) :
    Tcur*a-Tprev*b≤(198/29)*a*E := by
  have h1 := mul_nonneg ht (show 0≤b-a by linarith)
  have h2 := mul_nonneg ha (show 0≤(198/29)*E-S by linarith)
  nlinarith

theorem complete_C_payment (phi a b E Gcur Gprev Tcur Tprev : ℝ)
    (ha : 0<a) (he : 0<E) (hG : 0≤Gcur-phi*Gprev)
    (hres : (243/32)*a*E≤(phi*a-b)*Gprev)
    (hsource : Tcur*a-Tprev*b≤(198/29)*a*E) :
    0<(Gcur-Tcur)*a-(Gprev-Tprev)*b := by
  have h1 := mul_nonneg (le_of_lt ha) hG
  have hpos := mul_pos ha he
  have hid : (Gcur-Tcur)*a-(Gprev-Tprev)*b=
      a*(Gcur-phi*Gprev)+(phi*a-b)*Gprev-(Tcur*a-Tprev*b) := by ring
  nlinarith

theorem wedge_head_and_weight_geometry (u h r w delta n : ℤ)
    (_hu : 0≤u) (hr : 2*r≤h) (hw : w=u+r) (hd : delta=h-u)
    (hn : n=delta-2) (hdelta : 5≤delta) (hcone : 13*delta≤4*w+17) :
    h≤3*u+2 ∧ 17≤w+delta ∧ 3≤n ∧ 13*n+9≤4*w := by omega

#print axioms reference_amplification_all_large
#print axioms reference_mass_two_fifths
#print axioms interval_product_sum_margin
#print axioms reference_previous_read_budget
#print axioms finite_padding_positive_correction
#print axioms uniform_actual_golden_gap
#print axioms renewal_response_prefix_bound
#print axioms loss_cumulative_prefix_bound
#print axioms geometric_interval_lower
#print axioms all_distance_boundary_constant
#print axioms increasing_pair_source_bound
#print axioms complete_C_payment
#print axioms wedge_head_and_weight_geometry

end CountWedgeBoundaryPositive
