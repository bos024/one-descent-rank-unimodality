import Mathlib

set_option maxHeartbeats 0

namespace DividedCIPrimitive

theorem binary_first_primitive_head (U p c : ℝ)
    (hU : 4 ≤ U) (hp0 : 0 ≤ p) (hp2 : p ≤ 2) (hc : -1/6 ≤ c) :
    7/3 ≤ U*(U+1)/2-p*(U-1)
      +c*(U*(U-1)/2+p*(U-2))+p*c^2 := by
  let A:=U*(U-1)/2
  have hU0 : 0 ≤ U := by linarith only [hU]
  have hUm1 : 0 ≤ U-1 := by linarith only [hU]
  have hUm2 : 0 ≤ U-2 := by linarith only [hU]
  have hA : 0 ≤ A := div_nonneg (mul_nonneg hU0 hUm1) (by norm_num)
  have h1:=mul_nonneg (show 0 ≤ c+1/6 by linarith only [hc])
    (add_nonneg hA (mul_nonneg hp0 hUm2))
  have h2:=mul_nonneg (show 0 ≤ 2-p by linarith only [hp2])
    (show 0 ≤ (U-1)+(U-2)/6 by linarith only [hUm1,hUm2])
  have h3:=mul_nonneg hp0 (sq_nonneg c)
  have hbase : 7/3 ≤ (5*U^2-21*U+32)/12 := by
    nlinarith only [sq_nonneg (U-4),hU]
  have heq : U*(U+1)/2-p*(U-1)+c*(A+p*(U-2))+p*c^2
      = (5*U^2-21*U+32)/12
        +(c+1/6)*(A+p*(U-2))
        +(2-p)*((U-1)+(U-2)/6)+p*c^2 := by dsimp [A]; ring
  change 7/3 ≤ U*(U+1)/2-p*(U-1)+c*(A+p*(U-2))+p*c^2
  rw [heq]
  linarith only [hbase,h1,h2,h3]

theorem binary_second_primitive_head (U p c : ℝ)
    (hU : 6 ≤ U) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hc : c ≤ 1/6) :
    0 ≤ U*(U^3+5*U-18)/12-p*U*(2*U-5)*(U+1)/6
      +c*((p-1)*U*(U-1)/2+U-p*U*(U-1)*(U-2)/6) := by
  let A:=U*(U-1)/2
  let C:=U*(U-1)*(U-2)/6
  let H:=U*(2*U-5)*(U+1)/6
  let K:=(p-1)*A+U-p*C
  have hU0 : 0 ≤ U := by linarith only [hU]
  have hp0 : 0 ≤ p := by linarith only [hp1]
  have hUm1 : 0 ≤ U-1 := by linarith only [hU]
  have hUm2 : 0 ≤ U-2 := by linarith only [hU]
  have hUm3 : 0 ≤ U-3 := by linarith only [hU]
  have hUm5 : 0 ≤ U-5 := by linarith only [hU]
  have h2Um5 : 0 ≤ 2*U-5 := by linarith only [hU]
  have hUp1 : 0 ≤ U+1 := by linarith only [hU]
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hCA : 0 ≤ C-A := by
    have he : C-A=U*(U-1)*(U-5)/6 := by dsimp [C,A]; ring
    rw [he]
    positivity
  have hAU : 0 ≤ A-U := by
    have he : A-U=U*(U-3)/2 := by dsimp [A]; ring
    rw [he]
    positivity
  have hK : K ≤ 0 := by
    have hp:=add_nonneg (mul_nonneg hp0 hCA) hAU
    have he : -K=p*(C-A)+(A-U) := by dsimp [K]; ring
    rw [← he] at hp
    linarith only [hp]
  have hKlo : -p*C ≤ K := by
    have hp:=add_nonneg (mul_nonneg (show 0 ≤ p-1 by linarith only [hp1]) hA) hU0
    dsimp [K]
    linarith only [hp]
  have h1:=mul_nonneg (show 0 ≤ 1/6-c by linarith only [hc])
    (show 0 ≤ -K by linarith only [hK])
  have h2:=mul_nonneg (show 0 ≤ 2-p by linarith only [hp2]) hC
  have hpay : -C/3 ≤ c*K := by nlinarith only [h1,h2,hKlo]
  have h3:=mul_nonneg (show 0 ≤ 2-p by linarith only [hp2]) hH
  have hw : 0 ≤ U-6 := by linarith only [hU]
  have hcube : 0 ≤ (U-6)^3 := pow_nonneg hw _
  have hpoly : 0 ≤ 3*(U-6)^3+28*(U-6)^2+69*(U-6)+56 := by positivity
  have hlow:=mul_nonneg hU0 hpoly
  have heq : U*(U^3+5*U-18)/12-p*H+c*K
      = U*(3*(U-6)^3+28*(U-6)^2+69*(U-6)+56)/36
        +(2-p)*H+(c*K+C/3) := by dsimp [H,C]; ring
  have hfinal : 0 ≤ U*(U^3+5*U-18)/12-p*H+c*K := by
    rw [heq]
    linarith only [hlow,h3,hpay]
  convert hfinal using 1
  dsimp [H,K,A,C]
  ring

theorem nonempty_first_primitive_head (w E2 p c : ℝ)
    (hw : 6 ≤ w) (hE20 : 0 ≤ E2) (hE2 : E2 ≤ w^2/2)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2) (hc : -1/4 ≤ c) :
    3/2 ≤ w^2-E2-p*(w-1)+c*(E2+p*(w-2))+p*c^2 := by
  have h1:=mul_nonneg (show 0 ≤ c+1/4 by linarith only [hc])
    (add_nonneg hE20 (mul_nonneg hp0 (show 0 ≤ w-2 by linarith only [hw])))
  have h2:=mul_nonneg (show 0 ≤ 2-p by linarith only [hp2])
    (show 0 ≤ (w-1)+(w-2)/4 by linarith only [hw])
  have h3:=mul_nonneg hp0 (sq_nonneg c)
  have h4 : 0 ≤ (5/4)*(w^2/2-E2) := by nlinarith only [hE2]
  have hbase : 3/2 ≤ 3*w^2/8-5*w/2+3 := by
    nlinarith only [sq_nonneg (w-6),hw]
  have heq : w^2-E2-p*(w-1)+c*(E2+p*(w-2))+p*c^2
      = 3*w^2/8-5*w/2+3+(5/4)*(w^2/2-E2)
        +(2-p)*((w-1)+(w-2)/4)
        +(c+1/4)*(E2+p*(w-2))+p*c^2 := by ring
  rw [heq]
  linarith only [hbase,h1,h2,h3,h4]

theorem unperturbed_interval_junction_gap (U b B2 Bprev Bt D : ℝ)
    (hU : 5 ≤ U) (hb : 0 < b) (hbhi : b ≤ 3*U/2)
    (hD : U/2+2 ≤ D) (hB : U-1 ≤ Bprev)
    (hdef : D=b^2-2*B2) (hLC : b*Bt ≤ B2*Bprev) :
    U/3 ≤ b*Bprev-2*Bt := by
  have hD0 : 0 ≤ D := by linarith only [hD,hU]
  have hU1 : 0 ≤ U-1 := by linarith only [hU]
  have h1:=mul_nonneg (show 0 ≤ D-(U/2+2) by linarith only [hD]) hU1
  have h2:=mul_nonneg hD0 (show 0 ≤ Bprev-(U-1) by linarith only [hB])
  have h3:=mul_nonneg (show 0 ≤ U/3 by linarith only [hU])
    (show 0 ≤ 3*U/2-b by linarith only [hbhi])
  have hdefB:=congrArg (fun z : ℝ => z*Bprev) hdef
  have hpay : 0 ≤ b*((b*Bprev-2*Bt)-U/3) := by
    nlinarith only [h1,h2,h3,hLC,hdefB,hU]
  by_contra hbad
  have hneg:=mul_neg_of_pos_of_neg hb
    (show (b*Bprev-2*Bt)-U/3<0 by linarith only [hbad])
  linarith only [hpay,hneg]

theorem exact_perturbed_last_junction (U xp x xn b : ℝ)
    (hbase : 0 ≤ x^2-xp*xn) (hgap : U/30 ≤ b*xp-2*x) :
    1+U/30 ≤ (x-1)^2-xp*(xn-b) := by
  nlinarith only [hbase,hgap]

theorem entire_capacity_word_induction
    (P : List ℕ → ℕ → Prop)
    (hbase : ∀ U, 3 ≤ U → P [] U)
    (hstep : ∀ (t : ℕ) (V : List ℕ) (U : ℕ),
      3 ≤ t → (t-1)+(V.map (fun s => s-1)).sum+3 ≤ U →
      P V U → P (t::V) U) :
    ∀ (V : List ℕ) (U : ℕ), (∀ t ∈ V, 3 ≤ t) →
      (V.map (fun s => s-1)).sum+3 ≤ U → P V U := by
  intro V
  induction V with
  | nil =>
    intro U _ hU
    exact hbase U (by simpa using hU)
  | cons t V ih =>
    intro U hvalid hU
    have ht : 3 ≤ t := hvalid t (by simp)
    have htail : ∀ s ∈ V, 3 ≤ s := by
      intro s hs
      exact hvalid s (by simp [hs])
    have hsum : (t-1)+(V.map (fun s => s-1)).sum+3 ≤ U := by
      simpa using hU
    exact hstep t V U ht hsum (ih U htail (by omega))

#print axioms binary_first_primitive_head
#print axioms binary_second_primitive_head
#print axioms nonempty_first_primitive_head
#print axioms unperturbed_interval_junction_gap
#print axioms exact_perturbed_last_junction
#print axioms entire_capacity_word_induction

end DividedCIPrimitive
