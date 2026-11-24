import Mathlib

set_option maxHeartbeats 0

namespace WeightedDividedCI

theorem ordinary_first_head (v r q c : ℝ)
    (hv : 2 ≤ v) (hr : 0 ≤ r) (hvr : 3*r ≤ v-1)
    (hq0 : 0 ≤ q) (hq : q ≤ 2/3) (hc : -1/5 ≤ c) :
    (9*v^2-2*v+5)/5 ≤ (2*v+1)^2-(2-c)*(v^2+2*r+q*(2*v+1)) := by
  have h1:=mul_nonneg (show 0 ≤ c+1/5 by linarith only [hc])
    (show 0 ≤ v^2+2*r+q*(2*v+1) by positivity)
  have h2:=mul_nonneg (show 0 ≤ 2/3-q by linarith only [hq])
    (show 0 ≤ (11/5)*(2*v+1) by nlinarith only [hv])
  have h3 : 0 ≤ (22/15)*(v-1-3*r) := by nlinarith only [hvr]
  nlinarith only [h1,h2,h3]

theorem binary_first_primitive_head (u p c : ℝ)
    (hu : 2 ≤ u) (hp0 : 0 ≤ p) (hp : p ≤ 2) (hc : -1/6 ≤ c) :
    4 ≤ 2*u^2+4*u+1-4*p*u+2*p+c*(u^2+p*(2*u-3))+p*c^2 := by
  have hlin : 0 ≤ 2*u-3 := by linarith only [hu]
  have h1:=mul_nonneg (show 0 ≤ c+1/6 by linarith only [hc])
    (show 0 ≤ u^2+p*(2*u-3) by positivity)
  have h2:=mul_nonneg (show 0 ≤ 2-p by linarith only [hp])
    (show 0 ≤ (4*u-2)+(2*u-3)/6 by linarith only [hu])
  have h3:=mul_nonneg hp0 (sq_nonneg c)
  have hbase : 4 ≤ (11*u^2-28*u+36)/6 := by
    nlinarith only [sq_nonneg (u-2),hu]
  have heq : 2*u^2+4*u+1-4*p*u+2*p+c*(u^2+p*(2*u-3))+p*c^2
      = (11*u^2-28*u+36)/6+(c+1/6)*(u^2+p*(2*u-3))
        +(2-p)*((4*u-2)+(2*u-3)/6)+p*c^2 := by ring
  rw [heq]
  linarith only [hbase,h1,h2,h3]

theorem binary_second_primitive_head (u p c : ℝ)
    (hu : 6 ≤ u) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hc : c ≤ 1/6) :
    0 ≤ u^4/3+(2-4*p)*u^3/3+13*u^2/6+(-25/6+13*p/3)*u+p-2
      +c*(1+2*u-u^2+p*(-u/6+3*u^2/2-u^3/3)) := by
  let H:=u*(2*u^2-9*u+1)/6
  let K:=1+2*u-u^2-p*H
  let D:=(4*u^3-13*u-3)/3
  have hu0 : 0 ≤ u := by linarith only [hu]
  have hw : 0 ≤ u-6 := by linarith only [hu]
  have hHpoly : 0 ≤ 2*u^2-9*u+1 := by nlinarith only [sq_nonneg (u-6),hu]
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hD : 0 ≤ D := by
    have heq : D=(4*(u-6)^3+72*(u-6)^2+419*(u-6)+783)/3 := by dsimp [D]; ring
    rw [heq]; positivity
  have hK : K ≤ 0 := by
    have h1:=mul_nonneg (show 0 ≤ p-1 by linarith only [hp1]) hH
    have h2 : 0 ≤ u^2-2*u-1 := by nlinarith only [sq_nonneg (u-6),hu]
    dsimp [K]
    linarith only [h1,hH,h2]
  have hKlo : -2*u^3/3 ≤ K := by
    have h1:=mul_nonneg (show 0 ≤ 2-p by linarith only [hp2]) hH
    have heq : K+2*u^3/3=(2-p)*H+1+5*u/3+2*u^2 := by dsimp [K,H]; ring
    rw [← sub_nonneg]
    have : 0 ≤ K+2*u^3/3 := by rw [heq]; positivity
    linarith only [this]
  have hpay : -u^3/9 ≤ c*K := by
    have h1:=mul_nonneg (show 0 ≤ 1/6-c by linarith only [hc])
      (show 0 ≤ -K by linarith only [hK])
    nlinarith only [h1,hKlo]
  have h2:=mul_nonneg (show 0 ≤ 2-p by linarith only [hp2]) hD
  have hpoly : 0 ≤ 6*(u-6)^3+70*(u-6)^2+231*(u-6)+243 := by positivity
  have hbase:=mul_nonneg hu0 hpoly
  have heq : u^4/3+(2-4*p)*u^3/3+13*u^2/6+(-25/6+13*p/3)*u+p-2+c*K
      = u*(6*(u-6)^3+70*(u-6)^2+231*(u-6)+243)/18+(2-p)*D+(c*K+u^3/9) := by dsimp [D]; ring
  have hfinal : 0 ≤ u^4/3+(2-4*p)*u^3/3+13*u^2/6+(-25/6+13*p/3)*u+p-2+c*K := by
    rw [heq]; linarith only [hbase,h2,hpay]
  convert hfinal using 1
  dsimp [K,H]; ring

theorem nonempty_first_primitive_head (v r p c : ℝ)
    (hv : 4 ≤ v) (hr : 0 ≤ r) (hvr : 3*r ≤ v-1)
    (hp0 : 0 ≤ p) (hp : p ≤ 2) (hc : -1/5 ≤ c) :
    57/5 ≤ (2*v+1)^2-2*(v^2+2*r)-2*p*(2*v-1)
      +c*(v^2+2*r+p*(2*v-3))+p*c^2 := by
  have hlin : 0 ≤ 2*v-3 := by linarith only [hv]
  have h1:=mul_nonneg (show 0 ≤ c+1/5 by linarith only [hc])
    (show 0 ≤ v^2+2*r+p*(2*v-3) by positivity)
  have h2:=mul_nonneg (show 0 ≤ 2-p by linarith only [hp])
    (show 0 ≤ 2*(2*v-1)+(2*v-3)/5 by linarith only [hv])
  have h3:=mul_nonneg hp0 (sq_nonneg c)
  have h4 : 0 ≤ (22/15)*(v-1-3*r) := by nlinarith only [hvr]
  have hbase : 57/5 ≤ (27*v^2-94*v+115)/15 := by
    nlinarith only [sq_nonneg (v-4),hv]
  nlinarith only [h1,h2,h3,h4,hbase]

theorem unperturbed_interval_junction_gap (u b B2 Bprev Bt D : ℝ)
    (hu : 5 ≤ u) (hb : 0 < b) (hbhi : b ≤ 3*u)
    (hD : 2*u+5 ≤ D) (hB : 2*(u-1) ≤ Bprev)
    (hdef : D=b^2-4*B2) (hLC : b*Bt ≤ B2*Bprev) :
    4*u/3 ≤ b*Bprev-4*Bt := by
  have hD0 : 0 ≤ D := by linarith only [hD,hu]
  have h1:=mul_nonneg (show 0 ≤ D-(2*u+5) by linarith only [hD])
    (show 0 ≤ 2*(u-1) by linarith only [hu])
  have h2:=mul_nonneg hD0 (show 0 ≤ Bprev-2*(u-1) by linarith only [hB])
  have h3:=mul_nonneg (show 0 ≤ 4*u/3 by linarith only [hu])
    (show 0 ≤ 3*u-b by linarith only [hbhi])
  have hdefB:=congrArg (fun z : ℝ => z*Bprev) hdef
  have hpay : 0 ≤ b*((b*Bprev-4*Bt)-4*u/3) := by
    nlinarith only [h1,h2,h3,hLC,hdefB,hu]
  by_contra hbad
  have hneg:=mul_neg_of_pos_of_neg hb
    (show (b*Bprev-4*Bt)-4*u/3<0 by linarith only [hbad])
  linarith only [hpay,hneg]

theorem exact_perturbed_last_junction (u xp x xn b : ℝ)
    (hbase : 0 ≤ x^2-xp*xn) (hgap : 11*u/15 ≤ b*xp-4*x) :
    4+11*u/15 ≤ (x-2)^2-xp*(xn-b) := by
  nlinarith only [hbase,hgap]

#print axioms ordinary_first_head
#print axioms binary_first_primitive_head
#print axioms binary_second_primitive_head
#print axioms nonempty_first_primitive_head
#print axioms unperturbed_interval_junction_gap
#print axioms exact_perturbed_last_junction

end WeightedDividedCI
