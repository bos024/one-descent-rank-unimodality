import Mathlib

set_option maxHeartbeats 0

namespace PaddingThreeLocalPrefix

theorem relaxed_first_row_margin (u q a : ℝ)
    (hu : 7 ≤ u) (hq0 : 0 ≤ q) (hq : q ≤ 5/8)
    (ha0 : 0 ≤ a) (ha : a ≤ (u+3)/2) :
    0 ≤ (1-q)*u*(u-1)+2*a*((1-q)*u-q*a-1) := by
  let A:=(u+3)/2
  let f:=fun x : ℝ => (1-q)*u*(u-1)+2*x*((1-q)*u-q*x-1)
  have hA : 0 < A := by dsimp [A]; linarith only [hu]
  have hAa : 0 ≤ A-a := by dsimp [A]; linarith only [ha]
  have hf0 : 0 ≤ f 0 := by
    have hq1 : 0 ≤ 1-q := by linarith only [hq]
    have hu0 : 0 ≤ u := by linarith only [hu]
    have hu1 : 0 ≤ u-1 := by linarith only [hu]
    dsimp [f]
    simpa using mul_nonneg (mul_nonneg hq1 hu0) hu1
  have hqpoly : 0 ≤ (5/8-q)*(5*u^2+10*u+9) := by
    have hu0 : 0 ≤ u := by linarith only [hu]
    positivity
  have hbase : 0 ≤ 7*u^2-34*u-93 := by
    nlinarith only [sq_nonneg (u-7),hu]
  have hfA : 0 ≤ f A := by dsimp [f,A]; nlinarith only [hqpoly,hbase]
  have h1:=mul_nonneg hAa hf0
  have h2:=mul_nonneg ha0 hfA
  have h3 : 0 ≤ 2*q*A*a*(A-a) := by positivity
  have heq : A*f a=(A-a)*f 0+a*f A+2*q*A*a*(A-a) := by dsimp [f]; ring
  have hprod : 0 ≤ A*f a := by rw [heq]; linarith only [h1,h2,h3]
  exact nonneg_of_mul_nonneg_right hprod hA

theorem relaxed_interior_row_zero (u q a : ℝ)
    (hu : 4 ≤ u) (hqlo : 3/5 ≤ q) (hqhi : q ≤ 5/8)
    (hroot : q^2+q=1) (ha : a ≤ (u+3)/2) :
    (1-q)*(u+q+a) ≤ u-q := by
  have h1:=mul_nonneg (show 0 ≤ 1-q by linarith only [hqhi])
    (show 0 ≤ (u+3)/2-a by linarith only [ha])
  have h2:=mul_nonneg (show 0 ≤ 3*q-1 by linarith only [hqlo])
    (show 0 ≤ u-4 by linarith only [hu])
  nlinarith only [h1,h2,hroot,hqlo]

theorem relaxed_final_row_power (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 2/3) :
    ∀ k : ℕ, q^(6+k)*(12+3*(k:ℝ)/2+q) ≤ 4/3 := by
  intro k
  induction k with
  | zero =>
    have hpow:=pow_le_pow_left₀ hq0 hq 6
    have hlin : 0 ≤ 12+q := by positivity
    have h1:=mul_nonneg (show 0 ≤ (2/3:ℝ)^6-q^6 by linarith only [hpow]) hlin
    norm_num at h1 ⊢
    nlinarith only [h1,hq]
  | succ k ih =>
    have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
    have hpos : 0 ≤ 27/2+3*(k:ℝ)/2+q := by positivity
    have h1:=mul_nonneg (show 0 ≤ 2/3-q by linarith only [hq]) hpos
    have hlin : q*(27/2+3*(k:ℝ)/2+q) ≤ 12+3*(k:ℝ)/2+q := by
      nlinarith only [h1,hk,hq0]
    have h2:=mul_nonneg (pow_nonneg hq0 (6+k))
      (show 0 ≤ (12+3*(k:ℝ)/2+q)-q*(27/2+3*(k:ℝ)/2+q) by linarith only [hlin])
    have heq : q^(6+(k+1))*(12+3*((k+1:ℕ):ℝ)/2+q)
        =q^(6+k)*(q*(27/2+3*(k:ℝ)/2+q)) := by
      push_cast
      rw [show 6+(k+1)=(6+k)+1 by omega, pow_succ]
      ring
    change q^(6+(k+1))*(12+3*((k+1:ℕ):ℝ)/2+q) ≤ 4/3
    rw [heq]
    nlinarith only [h2,ih]

theorem binary_second_primitive_head (u p c : ℝ)
    (hu : 8 ≤ u) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hc : c ≤ 1/6) :
    let w:=u+1
    let a:=(u^2+u+4)/2
    let b:=(u^3+11*u+6)/6
    0 ≤ a^2+a-w*b-w-p*(a*w+a-w^2-b)+c*(w-a+p*(a-b)) := by
  dsimp only
  let w:=u+1
  let a:=(u^2+u+4)/2
  let b:=(u^3+11*u+6)/6
  let H:=a*w+a-w^2-b
  let K:=w-a+p*(a-b)
  have hu0 : 0 ≤ u := by linarith only [hu]
  have hx : 0 ≤ u-8 := by linarith only [hu]
  have hp0 : 0 ≤ p := by linarith only [hp1]
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have haw : 0 ≤ a-w := by dsimp [a,w]; nlinarith only [sq_nonneg (u-8),hu]
  have hba : 0 ≤ b-a := by
    have heq : b-a=(u-8)^3/6+7*(u-8)^2/2+76*(u-8)/3+63 := by dsimp [b,a]; ring
    rw [heq]; positivity
  have hH : 0 ≤ H := by
    have heq : H=198+427*(u-8)/6+17*(u-8)^2/2+(u-8)^3/3 := by dsimp [H,a,b,w]; ring
    rw [heq]; positivity
  have hK : K ≤ 0 := by
    have h1:=mul_nonneg hp0 hba
    dsimp [K]; linarith only [haw,h1]
  have hKlo : -p*b ≤ K := by
    have h1:=mul_nonneg (show 0 ≤ p-1 by linarith only [hp1]) ha0
    have hw : 0 ≤ w := by dsimp [w]; positivity
    dsimp [K]; nlinarith only [h1,hw]
  have hpay : -b/3 ≤ c*K := by
    have h1:=mul_nonneg (show 0 ≤ 1/6-c by linarith only [hc])
      (show 0 ≤ -K by linarith only [hK])
    have h2:=mul_nonneg (show 0 ≤ 2-p by linarith only [hp2]) hb0
    nlinarith only [h1,h2,hKlo]
  have h2:=mul_nonneg (show 0 ≤ 2-p by linarith only [hp2]) hH
  have hpoly : 0 ≤ 403/3+1699*(u-8)/18+271*(u-8)^2/12+41*(u-8)^3/18+(u-8)^4/12 := by positivity
  have heq : a^2+a-w*b-w-p*H+c*K
      =(403/3+1699*(u-8)/18+271*(u-8)^2/12+41*(u-8)^3/18+(u-8)^4/12)
        +(2-p)*H+(c*K+b/3) := by dsimp [H,a,b,w]; ring
  have hfinal : 0 ≤ a^2+a-w*b-w-p*H+c*K := by
    rw [heq]; linarith only [hpoly,h2,hpay]
  exact hfinal

theorem concave_junction_scalar (u r : ℝ)
    (hu : 8 ≤ u) (hr : 0 ≤ r) (hrr : 2*r ≤ u-3) :
    0 ≤ (u-r-4)*(r+2)*(u-1)-(u/2)*(u+r+1) := by
  let R:=(u-3)/2
  let F:=(u-r-4)*(r+2)*(u-1)-(u/2)*(u+r+1)
  let F0:=(3*u^2-21*u+16)/2
  let FR:=(u^3-8*u^2+5)/4
  have hR : 0 < R := by dsimp [R]; linarith only [hu]
  have hRr : 0 ≤ R-r := by dsimp [R]; linarith only [hrr]
  have hF0 : 0 ≤ F0 := by dsimp [F0]; nlinarith only [sq_nonneg (u-8),hu]
  have hFR : 0 ≤ FR := by
    have h1:=mul_nonneg (sq_nonneg u) (show 0 ≤ u-8 by linarith only [hu])
    dsimp [FR]; nlinarith only [h1]
  have h1:=mul_nonneg hRr hF0
  have h2:=mul_nonneg hr hFR
  have h3 : 0 ≤ R*(u-1)*r*(R-r) := by
    have hu1 : 0 ≤ u-1 := by linarith only [hu]
    positivity
  have heq : R*F=(R-r)*F0+r*FR+R*(u-1)*r*(R-r) := by dsimp [R,F,F0,FR]; ring
  have hprod : 0 ≤ R*F := by rw [heq]; linarith only [h1,h2,h3]
  exact nonneg_of_mul_nonneg_right hprod hR

theorem unperturbed_interval_junction_gap (u r b B2 Bprev Bt D : ℝ)
    (hu : 8 ≤ u) (hr : 0 ≤ r) (hrr : 2*r ≤ u-3)
    (hb : 0 < b) (hbhi : b ≤ u+r+1)
    (hD : u-r-4 ≤ D) (hB : (r+2)*(u-1) ≤ Bprev)
    (hdef : D=b^2-2*B2) (hLC : b*Bt ≤ B2*Bprev) :
    u/2 ≤ b*Bprev-2*Bt := by
  have hF:=concave_junction_scalar u r hu hr hrr
  have hDlo : 0 ≤ u-r-4 := by linarith only [hu,hrr]
  have hD0 : 0 ≤ D := by linarith only [hD,hDlo]
  have hB0 : 0 ≤ (r+2)*(u-1) := by
    have hu1 : 0 ≤ u-1 := by linarith only [hu]
    positivity
  have h1:=mul_nonneg (show 0 ≤ D-(u-r-4) by linarith only [hD]) hB0
  have h2:=mul_nonneg hD0 (show 0 ≤ Bprev-(r+2)*(u-1) by linarith only [hB])
  have h3:=mul_nonneg (show 0 ≤ u/2 by linarith only [hu])
    (show 0 ≤ u+r+1-b by linarith only [hbhi])
  have hdefB:=congrArg (fun z : ℝ => z*Bprev) hdef
  have hpay : 0 ≤ b*((b*Bprev-2*Bt)-u/2) := by
    nlinarith only [hF,h1,h2,h3,hLC,hdefB]
  by_contra hbad
  have hneg:=mul_neg_of_pos_of_neg hb (show (b*Bprev-2*Bt)-u/2<0 by linarith only [hbad])
  linarith only [hpay,hneg]

theorem exact_perturbed_last_junction (u xp x xn b : ℝ)
    (hbase : 0 ≤ x^2-xp*xn) (hgap : u/6 ≤ b*xp-2*x) :
    1+u/6 ≤ (x-1)^2-xp*(xn-b) := by
  nlinarith only [hbase,hgap]

#print axioms relaxed_first_row_margin
#print axioms relaxed_interior_row_zero
#print axioms relaxed_final_row_power
#print axioms binary_second_primitive_head
#print axioms concave_junction_scalar
#print axioms unperturbed_interval_junction_gap
#print axioms exact_perturbed_last_junction

end PaddingThreeLocalPrefix
