import Mathlib

set_option maxHeartbeats 0
namespace OneJumpReferenceC

theorem recurrence_minor_negates (a b c d : ℤ)
    (hc : c=a+b) (hd : d=b+c) : c^2-b*d= -(b^2-a*c) := by
  rw [hc,hd,hc]
  ring

theorem constant_shift_cumulative_minor (A B C c : ℝ) :
    (B-c)^2-(A-c)*(C-c)=B^2-A*C+c*(A+C-2*B) := by ring

theorem constant_shift_C_minor (A B C c : ℝ) :
    A*(C-c)-B*(B-c)= -(B^2-A*C)+c*(B-A) := by ring

theorem amplitude_budget (c f fp s : ℝ)
    (hc : 3 ≤ c) (hf : 0 ≤ f) (hfp : fp ≤ f) (hs : -1 ≤ s) :
    f+2*fp-1-s ≤ c*f := by
  have hp := mul_nonneg (show 0 ≤ c-3 by linarith) hf
  nlinarith only [hp,hfp,hs]

theorem bounded_amplitude_payment (det c r C f : ℝ)
    (hdet : -C ≤ det) (hc : 0 ≤ c) (hr : f ≤ r)
    (hbudget : C ≤ c*f) : 0 ≤ det+c*r := by
  have hp := mul_nonneg hc (sub_nonneg.mpr hr)
  nlinarith only [hp,hdet,hbudget]

theorem prefix_C_payment (k : ℕ) (fk fk1 sign : ℝ)
    (hk : 2 ≤ k) (hf : 1 ≤ fk) (hmono : fk ≤ fk1) (hs : sign ≤ 1) :
    0 ≤ (k:ℝ)*fk1-fk-sign := by
  have hkr : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hp := mul_nonneg (show 0 ≤ (k:ℝ)-2 by linarith)
    (show 0 ≤ fk1 by linarith)
  nlinarith only [hp,hmono,hf,hs]

theorem prefix_LC_payment (k : ℕ) (fk fk1 sign : ℝ)
    (hk : 3 ≤ k) (hf : 0 ≤ fk1) (hmono : fk ≤ fk1) (hs : -1 ≤ sign) :
    0 ≤ ((k:ℝ)-1)*fk1-2*fk+1+sign := by
  have hkr : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hp := mul_nonneg (show 0 ≤ (k:ℝ)-3 by linarith) hf
  nlinarith only [hp,hmono,hs]

#print axioms recurrence_minor_negates
#print axioms constant_shift_cumulative_minor
#print axioms constant_shift_C_minor
#print axioms amplitude_budget
#print axioms bounded_amplitude_payment
#print axioms prefix_C_payment
#print axioms prefix_LC_payment
end OneJumpReferenceC
