import Mathlib
set_option maxHeartbeats 4000000
namespace MixedThreeFourActualCut

theorem whole_small_norm_surplus_cone (b : ℝ) (r s : ℕ)
    (hb : 0≤b) (hb6 : b≤6/11) (hr : 3*s+8≤r) :
    b^(r+1)*(4:ℝ)^s<1/64 := by
  have hb1 : b≤1 := by linarith
  have he : 3*s+9≤r+1 := by omega
  have hpow := pow_le_pow_of_le_one hb hb1 he
  have hp : b^(r+1)*(4:ℝ)^s≤b^9*(4*b^3)^s := by
    have h := mul_le_mul_of_nonneg_right hpow (show 0≤(4:ℝ)^s by positivity)
    have hid : b^(3*s+9)=(b^3)^s*b^9 := by rw [pow_add,pow_mul]
    rw [hid] at h
    rw [mul_pow]
    nlinarith only [h]
  have hcube := pow_le_pow_left₀ hb hb6 3
  have hq : 4*b^3≤1 := by nlinarith only [hcube]
  have hqp : (4*b^3)^s≤1 := pow_le_one₀ (by positivity) hq
  have hp9 := pow_le_pow_left₀ hb hb6 9
  have hbudget := mul_le_mul_of_nonneg_left hqp (show 0≤b^9 by positivity)
  have hnumeric : (6/11:ℝ)^9<1/64 := by norm_num
  nlinarith only [hp,hp9,hbudget,hnumeric]

theorem whole_all_count_damped_minor_payment (b : ℝ) (s n : ℕ)
    (hb : 0≤b) (hb6 : b≤6/11) (hn : 3*s+9≤n) :
    10*(2:ℝ)^s*b^(n/2)<1 := by
  have hb1 : b≤1 := by linarith
  have he : 3*s+8≤2*(n/2) := by omega
  have hp := pow_le_pow_of_le_one hb hb1 he
  have hk : b^(2*(n/2))=(b^(n/2))^2 := by rw [Nat.mul_comm 2 (n/2),pow_mul]
  rw [hk,pow_add,pow_mul] at hp
  have h2 : ((2:ℝ)^s)^2=(4:ℝ)^s := by simp only [sq,← mul_pow]; norm_num
  have hsquare : (((2:ℝ)^s*b^(n/2))^2)≤b^8*(4*b^3)^s := by
    have h := mul_le_mul_of_nonneg_right hp (show 0≤(4:ℝ)^s by positivity)
    rw [mul_pow,h2,mul_pow]
    nlinarith only [h]
  have hc := pow_le_pow_left₀ hb hb6 3
  have hq : 4*b^3≤1 := by nlinarith only [hc]
  have hqp : (4*b^3)^s≤1 := pow_le_one₀ (by positivity) hq
  have hbd := mul_le_mul_of_nonneg_left hqp (show 0≤b^8 by positivity)
  have hp8 := pow_le_pow_left₀ hb hb6 8
  have hnum : (100:ℝ)*(6/11:ℝ)^8<1 := by norm_num
  have hlt : (10*((2:ℝ)^s*b^(n/2)))^2<1 := by
    nlinarith only [hsquare,hbd,hp8,hnum]
  nlinarith only [hlt,sq_nonneg (10*((2:ℝ)^s*b^(n/2))-1)]

theorem complete_gamma_quarter_box (R0 R1 B gamma : ℝ)
    (h0 : -(1/4)≤R0 ∧ R0≤1/4) (h1 : -(1/4)≤R1 ∧ R1≤1/4)
    (hB : 2≤B) (hg : gamma*B=R0+R1) :
    -(1/4)≤gamma ∧ gamma≤1/4 := by
  by_cases hpos : 0≤gamma
  · have h := mul_nonneg hpos (show 0≤B-2 by linarith)
    constructor <;> nlinarith only [h,hg,h0.2,h1.2,hpos]
  · have h := mul_nonneg (show 0≤-gamma by linarith) (show 0≤B-2 by linarith)
    constructor <;> nlinarith only [h,hg,h0.1,h1.1,hpos]

theorem entire_degree_one_cumulative_source_identity
    (R : Type*) [CommRing R] (z a b R0 R1 gamma : R)
    (hg : R0+R1=gamma*(1+a+b)) :
    (R0+R1*z)-gamma*(1+a*z+b*z^2)=
      (1-z)*((R0-gamma)+b*gamma*z) := by
  linear_combination z*hg

theorem cumulative_quotient_first_seed (w V0 q1 q2 : ℝ)
    (hw : 32 ≤ w) (hV : 1/2≤V0 ∧ V0≤3/2)
    (hq1 : w-3/2≤q1) (hq2 : q2≤w*(w+1)/2) :
    0≤(V0+q1)^2-V0*(V0+q1+q2) := by
  have hq0 : 0≤q1 := by linarith
  have hV0 : 0≤V0 := by linarith
  have hprod0 := mul_le_mul_of_nonneg_left hq2 hV0
  have hprod1 := mul_le_mul_of_nonneg_right hV.2 (show 0≤w*(w+1)/2 by positivity)
  have hprod2 := mul_nonneg (show 0≤q1-(w-3/2) by linarith) (show 0≤V0+q1 by linarith)
  have hprod3 := mul_nonneg (show 0≤w-3/2 by linarith) (show 0≤V0+q1-(w-1) by linarith)
  have hpoly : 0≤(w-1)*(w-3/2)-(3/2)*w*(w+1)/2 := by
    let x := w-32
    have hx : 0≤x := by dsimp [x]; linarith
    have he : w=32+x := by dsimp [x]; ring
    rw [he]; ring_nf; positivity
  nlinarith only [hprod0,hprod1,hprod2,hprod3,hpoly]

theorem complete_true_source_three_startup_budgets (w r : ℝ)
    (hw : 32 ≤ w) (hr : 0≤r) (hrw : r≤w) :
    let m1 := w+1
    let m2 := (w+1)*(w+2)/2
    let m3 := (w+1)*(w+2)*(w+3)/6-r
    4 ≤ m1 ∧ 4*m1 ≤ m2 ∧ 4*m2 ≤ m3 ∧
    m2 ≤ m1^2 ∧ m1*m3 ≤ m2^2 := by
  dsimp
  have w0 : 0≤w := by linarith
  have p0 := mul_nonneg (show 0≤w+1 by linarith) (show 0≤w-6 by linarith)
  have p1 : 0≤(w+1)*(w+2)*(w+3)/6-w-4*((w+1)*(w+2)/2) := by
    let x := w-32
    have hx : 0≤x := by dsimp [x]; linarith
    have he : w=32+x := by dsimp [x]; ring
    rw [he]; ring_nf; positivity
  have p2 : 0≤((w+1)*(w+2)/2)^2-(w+1)*((w+1)*(w+2)*(w+3)/6) := by
    have hid : ((w+1)*(w+2)/2)^2-(w+1)*((w+1)*(w+2)*(w+3)/6)=
      w*(w+1)^2*(w+2)/12 := by ring
    rw [hid]; positivity
  have p3 := mul_nonneg (show 0≤w+1 by linarith) hr
  refine ⟨by linarith,by nlinarith only [p0],by linarith,?_,?_⟩
  · nlinarith only [w0,sq_nonneg w]
  · nlinarith only [p2,p3]

theorem generic_signed_source_startup_minor (x y z p q t : ℝ)
    (hx : 0≤x) (hz : 0≤z) (hg : y≤2*x)
    (hp : 0≤p) (hq : 0≤q) (ht : 4*q≤t)
    (hsource : p*t≤q^2) (hM : 0≤y^2-x*z) :
    0≤(y-q)^2-(x-p)*(z-t) := by
  have h0 := mul_nonneg hx (show 0≤t-4*q by linarith)
  have h1 := mul_nonneg hq (show 0≤2*x-y by linarith)
  have h2 := mul_nonneg hp hz
  nlinarith only [h0,h1,h2,hsource,hM]

theorem complete_first_actual_defect_minor (x y z delta loss : ℝ)
    (hx : 0≤x) (hdelta : 0≤delta) (hg : y≤2*x)
    (hM : -x≤y^2-x*z) (hloss : 4*delta+1≤loss) :
    0≤(y-delta)^2-x*(z-loss) := by
  have h0 := mul_nonneg hx (show 0≤loss-4*delta-1 by linarith)
  have h1 := mul_nonneg hdelta (show 0≤2*x-y by linarith)
  nlinarith only [h0,h1,hM,sq_nonneg delta]

theorem entire_surplus_deletion_closure (r s : ℕ) (hr : 32≤r)
    (hs : 3*s+8≤r) :
    32≤r ∧ 3*(s-1)+8≤r ∧ (0<s → 3*(s-1)+8≤r) := by omega

#print axioms whole_small_norm_surplus_cone
#print axioms whole_all_count_damped_minor_payment
#print axioms complete_gamma_quarter_box
#print axioms entire_degree_one_cumulative_source_identity
#print axioms cumulative_quotient_first_seed
#print axioms complete_true_source_three_startup_budgets
#print axioms generic_signed_source_startup_minor
#print axioms complete_first_actual_defect_minor
#print axioms entire_surplus_deletion_closure
end MixedThreeFourActualCut
