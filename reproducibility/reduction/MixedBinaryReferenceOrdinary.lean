import Mathlib
set_option maxHeartbeats 2000000
namespace MixedBinaryReferenceOrdinary

theorem universal_four_terminal_ordinary_minors
    (w p v x y A : ℝ) (hw : 9 ≤ w)
    (hp0 : w-1 ≤ p) (hp1 : p ≤ w)
    (hv : w*(w-1)/2 ≤ v) (hx : w ≤ x) (hy : x ≤ y)
    (hA0 : 0 ≤ A) (hA1 : A ≤ x+2*y+p+1) :
    0 ≤ A ∧ 0 ≤ x+2*y+p+1-A ∧
    0 ≤ (p-3)*y+(p-1)*x+p*(p-1)-1+A ∧
    0 ≤ (v-p+3)*y-(2*p-1)*x-p*(p-1)+1-A := by
  have w0 : 0 ≤ w := by linarith
  have p0 : 0 ≤ p := by linarith
  have x0 : 0 ≤ x := by linarith
  have y0 : 0 ≤ y := by linarith
  have hcoef : w ≤ v-3*p+1 := by
    have h := mul_nonneg (show 0 ≤ w-9 by linarith) w0
    nlinarith only [h,hv,hp1]
  have hcoef0 : 0 ≤ v-p+1 := by linarith
  have hpp : 1 ≤ p*(p-1) := by
    have h := mul_nonneg (show 0 ≤ p-2 by linarith) (show 0 ≤ p+1 by linarith)
    nlinarith only [h]
  have hpart0 := mul_nonneg (show 0 ≤ p-3 by linarith) y0
  have hpart1 := mul_nonneg (show 0 ≤ p-1 by linarith) x0
  have hpart2 := mul_nonneg hcoef0 (show 0 ≤ y-x by linarith)
  have hpart3 := mul_nonneg (show 0 ≤ v-3*p+1-w by linarith) x0
  have hpart4 := mul_nonneg w0 (show 0 ≤ x-w by linarith)
  have hpart5 := mul_nonneg (show 0 ≤ w-p by linarith) (show 0 ≤ w+p by linarith)
  refine ⟨hA0, by linarith, ?_, ?_⟩
  · linarith only [hpart0,hpart1,hpp,hA0]
  · have hid : (v-p+3)*y-(2*p-1)*x-p*(p-1)+1-A =
        (x+2*y+p+1-A)+(v-p+1)*(y-x)+(v-3*p+1)*x-p^2 := by ring
    rw [hid]
    nlinarith only [hA1,hpart2,hpart3,hpart4,hpart5]

theorem exact_backward_cassini_three_corners
    (R : Type*) [CommRing R] (x y p v A : R) :
    (x+2*y+p+1)-(A)=x+2*y+p+1-A ∧
    (x+y+p)*p-y-(x+2*y+p+1-A)=
      (p-3)*y+(p-1)*x+p*(p-1)-1+A ∧
    y*v-x*p-((p-3)*y+(p-1)*x+p*(p-1)-1+A)=
      (v-p+3)*y-(2*p-1)*x-p*(p-1)+1-A := by
  constructor
  · ring
  constructor <;> ring

theorem complete_binary_defect_three_left_budgets (w r : ℝ)
    (hw : 8 ≤ w) (_hr : 0 ≤ r) (hrw : r ≤ w) :
    let B := w+2
    let C := w*(w+1)/2+2*w+5
    let D := w*(w+1)*(w+2)/6+w*(w+1)+5*w+11-r
    0 ≤ B-5 ∧ 0 ≤ C-4*B-1 ∧ 0 ≤ D-4*C-1 := by
  dsimp
  have hvar : 0 ≤ w-8 := by linarith
  have hc : 0 ≤ (8+(w-8))*(8+(w-8)+1)/2+2*(8+(w-8))+5-4*(8+(w-8)+2)-1 := by
    ring_nf
    nlinarith only [hvar,sq_nonneg (w-8)]
  have hd : 0 ≤ w*(w+1)*(w-4)/6-4*w-10 := by
    let a := w-8
    have ha : 0 ≤ a := hvar
    have he : w=8+a := by dsimp [a]; ring
    rw [he]
    ring_nf
    positivity
  constructor
  · linarith
  constructor
  · nlinarith only [hc]
  · nlinarith only [hd,hrw]

theorem complete_far_or_near_damping_domain (r s m : ℕ)
    (hr : 57 ≤ r) (hm : r+3 ≤ m) (htail : 3*s ≤ m+1) :
    3*s+9 ≤ m ∨ (18 ≤ s ∧ 3*s ≤ m+2) := by
  by_cases hs : s < 18
  · left; omega
  · right; omega

theorem full_ordinary_window_head_read_cover (r s n : ℕ)
    (hr : 57 ≤ r) (hs : 1 ≤ s)
    (_hn0 : r+s+3 ≤ n) (_hn1 : n ≤ 3*r+4*s) :
    n ≤ r+s+5 ∨
    (r+(s-1)+3 ≤ n-4 ∧ n-1 ≤ 3*r+4*(s-1)) ∨
    (3*r+4*s-3 ≤ n) := by
  omega

theorem complete_four_phase_protected_extension_cover (r s n : ℕ)
    (_hr : 1 ≤ r) (_hs : 1 ≤ s) (hphase : r+3 ≤ 3*s)
    (_hn : s+4 ≤ n) :
    n < r+s+2 → n ≤ 4*s-2 := by omega

theorem first_binary_defect_root_head_or_pure_tail (r s n : ℕ)
    (hr : 57 ≤ r) (hn : r+s+3 ≤ n) :
    (s+4 ≤ n ∧ n ≤ 4*s-2) ∨
    (4*s-2 ≤ n-1 ∧ r+3 ≤ n-s ∧ 3*s ≤ (n-s)+1) := by
  omega

theorem all_dense_actual_reference_and_late_C_join
    (r s u : ℕ) (C : ℕ → Prop)
    (hu : 2*r+3*s ≤ u+5)
    (hprotected : ∀ n, n ≤ u+r+s+3 → C n)
    (hlate : ∀ n, 3*r+4*s-1 ≤ n → C n) : ∀ n, C n := by
  intro n
  by_cases hn : n ≤ u+r+s+3
  · exact hprotected n hn
  · exact hlate n (by omega)

theorem one_edge_after_first_binary_defect_all_C
    (G H d e delta eta : ℝ)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hdouble : G ≤ 2*H)
    (hdelta : 0 ≤ delta) (hd : delta ≤ d) (heta : 3*delta ≤ eta)
    (hC : 0 ≤ G*d-H*e) :
    0 ≤ G*(d-delta)-H*max 0 (e-eta+delta) := by
  by_cases he : e-eta+delta ≤ 0
  · rw [max_eq_left he]
    simpa using mul_nonneg hG (show 0 ≤ d-delta by linarith)
  · rw [max_eq_right (by linarith : 0 ≤ e-eta+delta)]
    have h0 := mul_nonneg hdelta (show 0 ≤ 2*H-G by linarith)
    have h1 := mul_nonneg hH (show 0 ≤ eta-3*delta by linarith)
    nlinarith only [h0,h1,hC]

end MixedBinaryReferenceOrdinary
#print axioms MixedBinaryReferenceOrdinary.universal_four_terminal_ordinary_minors
#print axioms MixedBinaryReferenceOrdinary.exact_backward_cassini_three_corners
#print axioms MixedBinaryReferenceOrdinary.complete_binary_defect_three_left_budgets
#print axioms MixedBinaryReferenceOrdinary.complete_far_or_near_damping_domain
#print axioms MixedBinaryReferenceOrdinary.full_ordinary_window_head_read_cover
#print axioms MixedBinaryReferenceOrdinary.complete_four_phase_protected_extension_cover
#print axioms MixedBinaryReferenceOrdinary.first_binary_defect_root_head_or_pure_tail
#print axioms MixedBinaryReferenceOrdinary.all_dense_actual_reference_and_late_C_join
#print axioms MixedBinaryReferenceOrdinary.one_edge_after_first_binary_defect_all_C
