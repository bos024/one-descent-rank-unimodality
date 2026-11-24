import Mathlib

set_option maxHeartbeats 0

namespace ConvexTiltLagrangeSource

theorem background_right_ratio (X x Z R : ℝ) (hX : 0 < X)
    (hx : 0 ≤ x) (hlc : 0 ≤ x^2-X*Z) (hr : x ≤ R*X) : Z ≤ R*x := by
  have h1 := mul_nonneg hx (show 0 ≤ R*X-x by linarith only [hr])
  have hxx : X*Z ≤ X*(R*x) := by nlinarith only [hlc,h1]
  by_contra hh
  have hp := mul_pos hX (show 0 < Z-R*x by linarith only [hh])
  nlinarith only [hp,hxx]

theorem source_density_convex (X x Z em e ep R : ℝ)
    (hX : 0 < X) (hx : 0 < x) (hZ : 0 ≤ Z) (hem : 0 ≤ em)
    (hlc : 0 ≤ x^2-X*Z) (hr : x ≤ R*X)
    (hs : R*em ≤ e) (hc : 0 ≤ ep-2*R*e+R^2*em) :
    0 ≤ em*x*Z+ep*X*x-2*e*X*Z := by
  have hRZ := background_right_ratio X x Z R hX (le_of_lt hx) hlc hr
  let C := R^2*x*X-2*R*X*Z+x*Z
  have h1 : 0 ≤ X*(R*x-Z)^2+Z*(x^2-X*Z) := by positivity
  have hid : x*C=X*(R*x-Z)^2+Z*(x^2-X*Z) := by dsimp [C]; ring
  have hprod : 0 ≤ x*C := by rw [hid]; exact h1
  have hC : 0 ≤ C := (mul_nonneg_iff_of_pos_left hx).mp hprod
  have h2 : 0 ≤ X*x*(ep-2*R*e+R^2*em) := by positivity
  have h3 : 0 ≤ 2*X*(R*x-Z)*(e-R*em) := by
    have ha : 0 ≤ R*x-Z := by linarith only [hRZ]
    have hb : 0 ≤ e-R*em := by linarith only [hs]
    positivity
  have h4 := mul_nonneg hem hC
  have heq : em*x*Z+ep*X*x-2*e*X*Z
      =X*x*(ep-2*R*e+R^2*em)+2*X*(R*x-Z)*(e-R*em)+em*C := by
    dsimp [C]; ring
  rw [heq]
  linarith only [h2,h3,h4]

theorem concave_positive_part_LC (a b c : ℝ) (hc : a+c ≤ 2*b) :
    0 ≤ (max b 0)^2-max a 0*max c 0 := by
  by_cases ha : a≤0
  · rw [max_eq_right ha]; simp only [zero_mul,sub_zero]; exact sq_nonneg _
  by_cases hc0 : c≤0
  · rw [max_eq_right hc0]; simp only [mul_zero,sub_zero]; exact sq_nonneg _
  have ha0 : 0 < a := by linarith only [ha]
  have hcc : 0 < c := by linarith only [hc0]
  have hb : 0 ≤ b := by linarith only [ha0,hcc,hc]
  rw [max_eq_left hb,max_eq_left (le_of_lt ha0),max_eq_left (le_of_lt hcc)]
  have hp := mul_nonneg (le_of_lt ha0) (show 0 ≤ 2*b-a-c by linarith only [hc])
  nlinarith only [hp,sq_nonneg (b-a)]

theorem positive_scale_max (X e : ℝ) (hX : 0 < X) :
    max (X-e) 0=X*max (1-e/X) 0 := by
  have hne : X≠0 := ne_of_gt hX
  have heq : X*(1-e/X)=X-e := by field_simp
  by_cases hh : 0 ≤ 1-e/X
  · have hp := mul_nonneg (le_of_lt hX) hh
    have hraw : 0 ≤ X-e := by nlinarith only [heq,hp]
    rw [max_eq_left hraw,max_eq_left hh]
    exact heq.symm
  · have hnon : 1-e/X ≤0 := by linarith only [hh]
    have hp := mul_nonneg (le_of_lt hX) (show 0 ≤ -(1-e/X) by linarith only [hnon])
    have hraw : X-e ≤0 := by nlinarith only [heq,hp]
    rw [max_eq_right hraw,max_eq_right hnon,mul_zero]

theorem product_LC_triples (X x Z a b c : ℝ)
    (hX : 0 ≤ X) (hZ : 0 ≤ Z)
    (hx : 0 ≤ x^2-X*Z) (hb : 0 ≤ b^2-a*c) :
    0 ≤ (x*b)^2-(X*a)*(Z*c) := by
  have h1 := mul_nonneg (sq_nonneg b) hx
  have h2 := mul_nonneg (mul_nonneg hX hZ) hb
  nlinarith only [h1,h2]

theorem convex_tilt_source_positive_part_LC (X x Z em e ep R : ℝ)
    (hX : 0 < X) (hx : 0 < x) (hZ : 0 < Z) (hem : 0 ≤ em)
    (hlc : 0 ≤ x^2-X*Z) (hr : x ≤ R*X)
    (hs : R*em ≤ e) (hc : 0 ≤ ep-2*R*e+R^2*em) :
    0 ≤ (max (x-e) 0)^2-max (X-em) 0*max (Z-ep) 0 := by
  have hn := source_density_convex X x Z em e ep R hX hx (le_of_lt hZ) hem hlc hr hs hc
  let a := em/X
  let b := e/x
  let c := ep/Z
  have hid : X*x*Z*(a+c-2*b)=em*x*Z+ep*X*x-2*e*X*Z := by
    dsimp [a,b,c]
    field_simp
  have hden : 0 < X*x*Z := mul_pos (mul_pos hX hx) hZ
  have hp : 0 ≤ X*x*Z*(a+c-2*b) := by rw [hid]; exact hn
  have hconv : 0 ≤ a+c-2*b := (mul_nonneg_iff_of_pos_left hden).mp hp
  have hcomp := concave_positive_part_LC (1-a) (1-b) (1-c) (by linarith only [hconv])
  have hres := product_LC_triples X x Z (max (1-a) 0) (max (1-b) 0) (max (1-c) 0)
    (le_of_lt hX) (le_of_lt hZ) hlc hcomp
  rw [positive_scale_max x e hx,positive_scale_max X em hX,positive_scale_max Z ep hZ]
  exact hres

private theorem exponential_two_lower (k : ℕ) : (4:ℝ) ≤ 2^(k+2) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k+1+2=(k+2)+1 by omega,pow_succ]
    nlinarith only [ih]

theorem positive_lagrange_kernel_all_ranks (p : ℝ) (hp : p ≤13/8) :
    ∀ k : ℕ, 5/8 ≤ (5-3*p)*2^(k+2)-(2-p)*((k:ℝ)+2)+3*p-4 := by
  intro k
  induction k with
  | zero => norm_num; linarith only [hp]
  | succ k ih =>
    have hpow := exponential_two_lower k
    have ha : 0 ≤ 5-3*p := by linarith only [hp]
    have h1 := mul_nonneg ha (show 0 ≤ (2:ℝ)^(k+2)-4 by linarith only [hpow])
    rw [show k+1+2=(k+2)+1 by omega,pow_succ]
    push_cast
    nlinarith only [ih,h1,hp]

theorem higher_source_uniform_cut_payment (r p : ℝ)
    (hr : 4 ≤ r) (hp : p ≤13/8) :
    0 < (r-3)*(26-13*p)-r := by
  have h1 := mul_nonneg (show 0 ≤ r-3 by linarith only [hr])
    (show 0 ≤ 13/8-p by linarith only [hp])
  nlinarith only [h1,hr]

theorem interior_unit_budget (u q : ℝ) (hu : 12 ≤ u) (hq : q ≤2/3) :
    (u+2)^2*(u+q) ≤ 2*(u+1)*(u-1)*(u-2) := by
  have hx : 0 ≤ u-12 := by linarith only [hu]
  have hc : 0 ≤ (u-12)^3 := by positivity
  have hs := sq_nonneg (u-12)
  have h1 := mul_nonneg (show 0 ≤ 2/3-q by linarith only [hq]) (sq_nonneg (u+2))
  nlinarith only [hc,hs,hx,h1]

theorem unit_zero_row (u : ℝ) (hu : 12 ≤ u) :
    4*u/3+5/3 ≤ (u-1)*(u-2)/2 := by
  nlinarith only [sq_nonneg (u-12),hu]

theorem small_count_norm : (21/8:ℝ)*(27/40)^4 ≤3/5 := by norm_num

theorem small_count_nonlong_geometry (u delta r t : ℝ)
    (hr : 4 ≤ r) (hd : 3 ≤ delta)
    (hold : (r-1)*delta ≤ u+delta-t+1) :
    t ≤ u-5 := by
  have hd0 : 0 ≤ delta := by linarith only [hd]
  have h1 := mul_nonneg (show 0 ≤ r-4 by linarith only [hr]) hd0
  nlinarith only [h1,hd,hold]

theorem all_nonlong_junction_scalar (u r : ℝ)
    (hu : 12 ≤ u) (hr : 3 ≤r) (hrr : 3*r ≤u) :
    0 ≤ (u-r-1)*(r+1)*(u-1)-(3/2)*u*(u+r) := by
  let S := u/3-3
  let w := r-3
  let F := (u-r-1)*(r+1)*(u-1)-(3/2)*u*(u+r)
  let F1 := (5*u^2-49*u+32)/2
  let FR := (2*u^3-17*u^2-12*u+9)/9
  have hS : 0 < S := by dsimp [S]; linarith only [hu]
  have hw : 0 ≤w := by dsimp [w]; linarith only [hr]
  have hSw : 0 ≤S-w := by dsimp [S,w]; linarith only [hrr]
  have hu1 : 0 ≤u-1 := by linarith only [hu]
  have hF1 : 0 ≤F1 := by dsimp [F1]; nlinarith only [sq_nonneg (u-12),hu]
  have hx : 0 ≤u-12 := by linarith only [hu]
  have hc : 0 ≤(u-12)^3 := by positivity
  have hFR : 0 ≤FR := by
    dsimp [FR]
    nlinarith only [hc,sq_nonneg (u-12),hx]
  have h1 := mul_nonneg hSw hF1
  have h2 := mul_nonneg hw hFR
  have h3 : 0 ≤S*(u-1)*w*(S-w) := by positivity
  have heq : S*F=(S-w)*F1+w*FR+S*(u-1)*w*(S-w) := by
    dsimp [S,w,F,F1,FR]; ring
  have hprod : 0 ≤S*F := by rw [heq]; linarith only [h1,h2,h3]
  exact nonneg_of_mul_nonneg_right hprod hS

theorem all_nonlong_junction_gap (u r b B2 Bprev Bt D : ℝ)
    (hu : 12 ≤ u) (hr : 3 ≤r) (hrr : 3*r ≤u)
    (hb : 0 < b) (hbhi : b ≤u+r)
    (hD : u-r-1 ≤D) (hB : (r+1)*(u-1) ≤Bprev)
    (hdef : D=b^2-2*B2) (hLC : b*Bt ≤B2*Bprev) :
    3*u/2 ≤ b*Bprev-2*Bt := by
  have hF := all_nonlong_junction_scalar u r hu hr hrr
  have hrlo : 0 ≤r := by linarith only [hr]
  have hDlo : 0 ≤u-r-1 := by linarith only [hu,hrr]
  have hD0 : 0 ≤D := by linarith only [hD,hDlo]
  have hu1 : 0 ≤u-1 := by linarith only [hu]
  have hB0 : 0 ≤(r+1)*(u-1) := by positivity
  have h1 := mul_nonneg (show 0 ≤D-(u-r-1) by linarith only [hD]) hB0
  have h2 := mul_nonneg hD0 (show 0 ≤Bprev-(r+1)*(u-1) by linarith only [hB])
  have h3 := mul_nonneg (show 0 ≤3*u/2 by linarith only [hu])
    (show 0 ≤u+r-b by linarith only [hbhi])
  have hdefB := congrArg (fun z : ℝ => z*Bprev) hdef
  have hpay : 0 ≤ b*((b*Bprev-2*Bt)-3*u/2) := by
    nlinarith only [hF,h1,h2,h3,hLC,hdefB]
  have hres := (mul_nonneg_iff_of_pos_left hb).mp hpay
  linarith only [hres]

theorem small_count_perturbed_junction (u gap err M : ℝ)
    (hu : 12 ≤u) (hg : 3*u/2 ≤gap)
    (he : err ≤4*u/5+2/5) (hm : 0 ≤M) :
    0 < M+1+gap-err := by linarith only [hu,hg,he,hm]

#print axioms background_right_ratio
#print axioms source_density_convex
#print axioms concave_positive_part_LC
#print axioms positive_scale_max
#print axioms product_LC_triples
#print axioms convex_tilt_source_positive_part_LC
#print axioms positive_lagrange_kernel_all_ranks
#print axioms higher_source_uniform_cut_payment
#print axioms interior_unit_budget
#print axioms unit_zero_row
#print axioms small_count_norm
#print axioms small_count_nonlong_geometry
#print axioms all_nonlong_junction_scalar
#print axioms all_nonlong_junction_gap
#print axioms small_count_perturbed_junction

end ConvexTiltLagrangeSource
