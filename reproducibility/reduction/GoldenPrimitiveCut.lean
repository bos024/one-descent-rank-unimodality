import Mathlib

set_option maxHeartbeats 0

namespace GoldenPrimitiveCut

theorem constant_cut_preserves_LC (a x b T : ℝ)
    (hT : 0 ≤ T) (ha : T ≤ a) (hLC : 0 ≤ x^2-a*b) :
    0 ≤ (x-T)^2-(a-T)*(b-T) := by
  by_cases hmid : 0 ≤ 2*x-a-b
  · have h1:=mul_nonneg (show 0 ≤ a-T by linarith only [ha]) hmid
    nlinarith only [h1,sq_nonneg (x-a)]
  · have h1:=mul_nonneg hT (show 0 ≤ a+b-2*x by linarith only [hmid])
    nlinarith only [hLC,h1]

theorem signed_primitive_cut_identity (q x b S d : ℝ)
    (hroot : q^2+q=1) :
    q^2*(x-((q+1)*b-(q+1)*S-q*d))
      =(q^2*x-q*b)+q*S+q^3*d := by
  linear_combination (S-b)*q*hroot

theorem first_source_minor_payment (M cp c w p : ℝ)
    (hM : 0 ≤ M) (hcp : 0 ≤ cp) (hw : 8 ≤ w)
    (hp : p ≤ 5/3) (hR : c ≤ p*cp) :
    1 ≤ M+cp*w-2*c+1 := by
  have h1:=mul_nonneg hcp (show 0 ≤ w-2*p by linarith only [hw,hp])
  nlinarith only [hM,h1,hR]

theorem second_source_minor_payment (M cp c cn w p E2 : ℝ)
    (hM : 0 ≤ M) (hcp : 0 ≤ cp) (hcn : 0 ≤ cn)
    (hw : 8 ≤ w) (hp : p ≤ 5/3) (hR : c ≤ p*cp)
    (hE2lo : w*(w-1)/2 ≤ E2) (hE2hi : E2 ≤ w^2) :
    0 ≤ M+cp*E2-2*w*c+cn+w^2-E2 := by
  have hw0 : 0 ≤ w := by linarith only [hw]
  have h1:=mul_nonneg (show 0 ≤ 5/3-p by linarith only [hp]) hw0
  have hpoly : 0 ≤ w*(w-1)/2-10*w/3 := by nlinarith only [sq_nonneg (w-8),hw]
  have hhead : 0 ≤ E2-2*p*w := by nlinarith only [h1,hpoly,hE2lo]
  have h2:=mul_nonneg hcp hhead
  have h3:=mul_nonneg (show 0 ≤ 2*w by linarith only [hw])
    (show 0 ≤ p*cp-c by linarith only [hR])
  nlinarith only [hM,hcn,hE2hi,h2,h3]

#print axioms constant_cut_preserves_LC
#print axioms signed_primitive_cut_identity
#print axioms first_source_minor_payment
#print axioms second_source_minor_payment

end GoldenPrimitiveCut
