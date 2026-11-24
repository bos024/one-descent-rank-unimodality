import Mathlib

set_option maxHeartbeats 0

namespace DoubleSubdegreeCI

theorem golden_sharp_fifteenth_power (q : ℝ) (hq0 : 0 ≤ q)
    (hroot : q^2+q=1) : q^15 ≤ 1/1360 := by
  have h2 : q^2=1-q := by linarith only [hroot]
  have h3 : q^3=2*q-1 := by
    calc q^3=q*q^2 := by ring
         _=q*(1-q) := by rw [h2]
         _=2*q-1 := by nlinarith only [h2]
  have h5 : q^5=5*q-3 := by
    calc q^5=q^2*q^3 := by ring
         _=(1-q)*(2*q-1) := by rw [h2,h3]
         _=5*q-3 := by nlinarith only [h2]
  have h15 : q^15=610*q-377 := by
    calc q^15=(q^5)^3 := by ring
         _=(5*q-3)^3 := by rw [h5]
         _=610*q-377 := by nlinarith only [h2,h3]
  have hhi : q ≤ 618033989/1000000000 := by
    by_contra hbad
    have h1 : 0 < q-618033989/1000000000 := by linarith only [hbad]
    have h2p : 0 < q+618033989/1000000000+1 := by linarith only [hq0]
    have hp := mul_pos h1 h2p
    nlinarith only [hp,hroot]
  linarith only [h15,hhi]

theorem octuple_rank_two_first (u q : ℝ) (hu : 16 ≤ u)
    (hq0 : 0 ≤ q) (hroot : q^2+q=1) :
    let q1 := u-q
    let q2 := u*(u-1)/2-q*q1
    let q3 := u*(u-1)*(u-2)/6-q*q2
    8*q^2*(q2+2*q*q1+q^2) ≤ q2*q1-q3 := by
  dsimp
  have h2 : q^2=1-q := by linarith only [hroot]
  have h3 : q^3=2*q-1 := by
    calc q^3=q*q^2 := by ring
         _=q*(1-q) := by rw [h2]
         _=2*q-1 := by nlinarith only [h2]
  let x := u-16
  have hx : 0 ≤ x := by dsimp [x]; linarith only [hu]
  have heq : 12*((u*(u-1)/2-q*(u-q))*(u-q)
      -(u*(u-1)*(u-2)/6-q*(u*(u-1)/2-q*(u-q)))
      -8*q^2*((u*(u-1)/2-q*(u-q))+2*q*(u-q)+q^2))
      =(1344+5184*(q+1))+(788+900*(q+1))*x
        +(108+36*(q+1))*x^2+4*x^3 := by
    dsimp [x]
    ring_nf
    simp only [h2,h3]
    ring
  have hp : 0 ≤ (1344+5184*(q+1))+(788+900*(q+1))*x
        +(108+36*(q+1))*x^2+4*x^3 := by positivity
  nlinarith only [heq,hp]

theorem octuple_rank_two_second (u q : ℝ) (hu : 16 ≤ u)
    (hq0 : 0 ≤ q) (hroot : q^2+q=1) :
    let q1 := u-q
    let q2 := u*(u-1)/2-q*q1
    let q3 := u*(u-1)*(u-2)/6-q*q2
    8*q^2*(q3+2*q*q2+q^2*q1) ≤ q2^2-q3*q1 := by
  dsimp
  have h2 : q^2=1-q := by linarith only [hroot]
  have h3 : q^3=2*q-1 := by
    calc q^3=q*q^2 := by ring
         _=q*(1-q) := by rw [h2]
         _=2*q-1 := by nlinarith only [h2]
  let x := u-16
  have hx : 0 ≤ x := by dsimp [x]; linarith only [hu]
  have heq : 12*((u*(u-1)/2-q*(u-q))^2
      -(u*(u-1)*(u-2)/6-q*(u*(u-1)/2-q*(u-q)))*(u-q)
      -8*q^2*((u*(u-1)*(u-2)/6-q*(u*(u-1)/2-q*(u-q)))
        +2*q*(u*(u-1)/2-q*(u-q))+q^2*(u-q)))
      =(11520+12960*(q+1))+(2688+4554*(q+1))*x
        +(443+426*(q+1))*x^2+(36+12*(q+1))*x^3+x^4 := by
    dsimp [x]
    ring_nf
    simp only [h2,h3]
    ring
  have hp : 0 ≤ (11520+12960*(q+1))+(2688+4554*(q+1))*x
        +(443+426*(q+1))*x^2+(36+12*(q+1))*x^3+x^4 := by positivity
  nlinarith only [heq,hp]

theorem octuple_interior_and_rows (u q : ℝ)
    (hu : 16 ≤ u) (hq : q ≤ 2/3) :
    6*(u+q) ≤ (u-1)*(u-2)/2 ∧
    8*(u+q) ≤ (u-1)*(u-2)*(u-3)/6 ∧
    (2/5)*(12*u+8+8*q) ≤ (u-1)*(u-2)/2 ∧
    (12*u+8+8*q)/16 ≤ u-q ∧
    12*u+8+8*q ≤ u*(u+1) ∧
    (3/16)*(u+q) ≤ u-q := by
  have hu0 : 0 ≤ u-16 := by linarith only [hu]
  have hsq := sq_nonneg (u-16)
  have hcub : 0 ≤ (u-16)^3 := by positivity
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · nlinarith only [hsq,hu,hq]
  · nlinarith only [hcub,hsq,hu,hq]
  · nlinarith only [hsq,hu,hq]
  · linarith only [hu,hq]
  · nlinarith only [hsq,hu,hq]
  · linarith only [hu,hq]

theorem octuple_quadratic_geometric_decay (q : ℝ) (hq0 : 0 ≤ q)
    (hq : q ≤ 2/3) (hpow : q^15 ≤ 1/1360) :
    ∀ k : ℕ, (((k:ℝ)+16)*((k:ℝ)+17))*q^(k+15) ≤ 1/5 := by
  intro k
  induction k with
  | zero => norm_num; nlinarith only [hpow]
  | succ k ih =>
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have h1:=mul_nonneg (show 0 ≤ 2/3-q by linarith only [hq])
      (show 0 ≤ (k:ℝ)+18 by linarith only [hk])
    have hf : q*((k:ℝ)+18) ≤ (k:ℝ)+16 := by nlinarith only [h1,hk]
    have h2:=mul_nonneg (show 0 ≤ (k:ℝ)+17 by linarith only [hk])
      (show 0 ≤ (k:ℝ)+16-q*((k:ℝ)+18) by linarith only [hf])
    have h3:=mul_nonneg (pow_nonneg hq0 (k+15)) h2
    have heq : ((((k+1:ℕ):ℝ)+16)*(((k+1:ℕ):ℝ)+17))*q^(k+1+15)
        =q^(k+15)*(((k:ℝ)+17)*(q*((k:ℝ)+18))) := by
      rw [show k+1+15=(k+15)+1 by omega,pow_succ]
      push_cast
      ring
    rw [heq]
    nlinarith only [h3,ih]

theorem double_subdegree_junction_scalar (u r : ℝ)
    (hu : 16 ≤ u) (hr : 1 ≤ r) (hrr : 2*r ≤ u) :
    0 ≤ (u-r-1)*(r+1)*(u-1)-(3/2)*u*(u+r) := by
  let S := u/2-1
  let w := r-1
  let F := (u-r-1)*(r+1)*(u-1)-(3/2)*u*(u+r)
  let F1 := (u^2-15*u+8)/2
  let FR := (u^3-10*u^2-4*u+4)/4
  have hS : 0 < S := by dsimp [S]; linarith only [hu]
  have hw : 0 ≤ w := by dsimp [w]; linarith only [hr]
  have hSw : 0 ≤ S-w := by dsimp [S,w]; linarith only [hrr]
  have hu1 : 0 ≤ u-1 := by linarith only [hu]
  have hF1 : 0 ≤ F1 := by dsimp [F1]; nlinarith only [sq_nonneg (u-16),hu]
  have h16 : 0 ≤ u-16 := by linarith only [hu]
  have hpoly : 0 ≤ u^3-10*u^2-4*u+4 := by
    have hcube : 0 ≤ (u-16)^3 := by positivity
    nlinarith only [hcube,sq_nonneg (u-16),h16]
  have hFR : 0 ≤ FR := by dsimp [FR]; positivity
  have h1 := mul_nonneg hSw hF1
  have h2 := mul_nonneg hw hFR
  have h3 : 0 ≤ S*(u-1)*w*(S-w) := by positivity
  have heq : S*F=(S-w)*F1+w*FR+S*(u-1)*w*(S-w) := by
    dsimp [S,w,F,F1,FR]; ring
  have hprod : 0 ≤ S*F := by rw [heq]; linarith only [h1,h2,h3]
  exact nonneg_of_mul_nonneg_right hprod hS

theorem double_subdegree_junction_gap (u r b B2 Bprev Bt D : ℝ)
    (hu : 16 ≤ u) (hr : 1 ≤ r) (hrr : 2*r ≤ u)
    (hb : 0 < b) (hbhi : b ≤ u+r)
    (hD : u-r-1 ≤ D) (hB : (r+1)*(u-1) ≤ Bprev)
    (hdef : D=b^2-2*B2) (hLC : b*Bt ≤ B2*Bprev) :
    3*u/2 ≤ b*Bprev-2*Bt := by
  have hF:=double_subdegree_junction_scalar u r hu hr hrr
  have hDlo : 0 ≤ u-r-1 := by linarith only [hu,hrr]
  have hD0 : 0 ≤ D := by linarith only [hD,hDlo]
  have hu1 : 0 ≤ u-1 := by linarith only [hu]
  have hr1 : 0 ≤ r+1 := by linarith only [hr]
  have hB0 : 0 ≤ (r+1)*(u-1) := by positivity
  have h1:=mul_nonneg (show 0 ≤ D-(u-r-1) by linarith only [hD]) hB0
  have h2:=mul_nonneg hD0 (show 0 ≤ Bprev-(r+1)*(u-1) by linarith only [hB])
  have h3:=mul_nonneg (show 0 ≤ 3*u/2 by linarith only [hu])
    (show 0 ≤ u+r-b by linarith only [hbhi])
  have hdefB:=congrArg (fun z : ℝ => z*Bprev) hdef
  have hpay : 0 ≤ b*((b*Bprev-2*Bt)-3*u/2) := by
    nlinarith only [hF,h1,h2,h3,hLC,hdefB]
  have hres := (mul_nonneg_iff_of_pos_left hb).mp hpay
  linarith only [hres]

theorem perturbed_junction (u gap err M : ℝ)
    (hu : 16 ≤ u) (hg : 3*u/2 ≤ gap)
    (he : err ≤ 6*u/5+8/15) (hm : 0 ≤ M) :
    0 < M+1+gap-err := by linarith only [hu,hg,he,hm]

theorem negative_initial_atom_is_absent (a n : ℤ) (h : a < n)
    (K : ℤ → ℝ) (hK : ∀ j, a < j → K j=0)
    (f g : ℕ → ℝ) (hfg : ∀ j, j≠0 → f j=g j) (L : ℕ) :
    (∑ j ∈ Finset.range L, K (n-(j:ℤ))*f j)
      = ∑ j ∈ Finset.range L, K (n-(j:ℤ))*g j := by
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hz : j=0
  · subst j
    simp only [Nat.cast_zero,sub_zero,hK n h,zero_mul]
  · rw [hfg j hz]

theorem long_three_endpoint_minor (u a b c : ℝ)
    (hu : 0 ≤ u) (ha0 : 0 ≤ a) (_hc0 : 0 ≤ c)
    (ha : a ≤ u^2) (hb : 3*u/2 ≤ b) (hc : c ≤ 1) :
    0 ≤ b^2-a*c := by
  have h1:=mul_nonneg ha0 (show 0 ≤ 1-c by linarith only [hc])
  have hb0 : 0 ≤ b := by linarith only [hu,hb]
  have h2:=mul_nonneg (show 0 ≤ b-3*u/2 by linarith only [hb])
    (show 0 ≤ b+3*u/2 by linarith only [hb0,hu])
  nlinarith only [h1,h2,ha,sq_nonneg u]

theorem long_four_endpoint_minor (u a b c : ℝ)
    (hu : 0 ≤ u) (ha0 : 0 ≤ a) (_hc0 : 0 ≤ c)
    (ha : a ≤ u^3/3) (hb : 2*u^2/3 ≤ b) (hc : c ≤ 3*u/4) :
    0 ≤ b^2-a*c := by
  have h1:=mul_nonneg ha0 (show 0 ≤ 3*u/4-c by linarith only [hc])
  have h2:=mul_nonneg (show 0 ≤ u^3/3-a by linarith only [ha])
    (show 0 ≤ 3*u/4 by linarith only [hu])
  have hb0 : 0 ≤ b := by nlinarith only [hb,sq_nonneg u]
  have h3:=mul_nonneg (show 0 ≤ b-2*u^2/3 by linarith only [hb])
    (show 0 ≤ b+2*u^2/3 by positivity)
  nlinarith only [h1,h2,h3,sq_nonneg (u^2)]

theorem first_primitive_minor (w c p E2 : ℝ)
    (hw : 18 ≤ w) (hc : 0 ≤ c) (hp0 : 0 ≤ p) (hp : p ≤ 2)
    (he0 : 0 ≤ E2) (he : E2 ≤ w^2/2) :
    0 < w^2-E2-p*(w-1)+c*(E2+p*(w-2))+p*c^2 := by
  have hw0 : 0 ≤ w-1 := by linarith only [hw]
  have hw2 : 0 ≤ w-2 := by linarith only [hw]
  have h1:=mul_nonneg (show 0 ≤ 2-p by linarith only [hp]) hw0
  have h2 : 0 ≤ c*(E2+p*(w-2)) := by positivity
  have h3 : 0 ≤ p*c^2 := by positivity
  nlinarith only [h1,h2,h3,he,sq_nonneg (w-18),hw]

theorem actual_ordinary_seed_losses (x y A w : ℝ)
    (hx : 0 < x) (hxy : x ≤ y) (hA : 0 < A) (hw : 4 ≤ w) :
    0 < A-4*x+(2*w-1)*y+4 ∧
    0 < A-2*x+(w+1)*y+1 ∧
    0 < A-2*x+w*y+1 := by
  have hy : 0 ≤ y := by linarith only [hx,hxy]
  have h1:=mul_nonneg (show 0 ≤ w-4 by linarith only [hw]) hy
  constructor
  · nlinarith only [h1,hx,hxy,hA]
  constructor <;> nlinarith only [h1,hx,hxy,hA]

#print axioms golden_sharp_fifteenth_power
#print axioms octuple_rank_two_first
#print axioms octuple_rank_two_second
#print axioms octuple_interior_and_rows
#print axioms octuple_quadratic_geometric_decay
#print axioms double_subdegree_junction_scalar
#print axioms double_subdegree_junction_gap
#print axioms perturbed_junction
#print axioms negative_initial_atom_is_absent
#print axioms long_three_endpoint_minor
#print axioms long_four_endpoint_minor
#print axioms first_primitive_minor
#print axioms actual_ordinary_seed_losses

end DoubleSubdegreeCI
