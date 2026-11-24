import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

namespace UniversalLateCFirstCrossing

theorem crossing_read_guards (u h r t a L b : ℕ)
    (hu : 5 ≤ u) (hr : 1 ≤ r) (hhlo : 2*r ≤ h) (hhhi : h ≤ u)
    (ha : a=h+r) (hL : L=u+r+1) (hb : b=a+t)
    (hcross : u+2 ≤ h+t) :
    6 ≤ u+r ∧ 3 ≤ a ∧ a+1 ≤ L ∧ L+1 ≤ b := by omega

theorem golden_endpoint_cross (p lp l rp r : ℝ)
    (hlp : 0<lp) (hrp : 0<rp)
    (hl : p*lp<l) (hr : r<p*rp) :
    r*lp<l*rp := by
  have h1 := mul_pos hlp (show 0<p*rp-r by linarith)
  have h2 := mul_pos hrp (show 0<l-p*lp by linarith)
  nlinarith

theorem strict_subtracted_window_ratio (A B lp l rp r mu p : ℝ)
    (hA : 0<A) (hrp : 0<rp) (hAd : A=rp-lp) (hBd : B=r-l)
    (hmu : B=mu*A) (hc : r*lp<l*rp) (hr : r<p*rp) :
    0<r-mu*rp ∧ mu<p := by
  have hid : A*(r-mu*rp)=l*rp-r*lp := by
    calc
      A*(r-mu*rp)=A*r-(mu*A)*rp := by ring
      _=A*r-B*rp := by rw [←hmu]
      _=l*rp-r*lp := by rw [hAd,hBd]; ring
  have hpos : 0<r-mu*rp := by nlinarith
  constructor <;> nlinarith

theorem full_alternating_partial_margin (q H : ℝ) (T : ℕ → ℝ)
    (hq0 : 0 ≤ q) (heq : q^2+q=1) (hH : 0<H)
    (h0 : T 0=H) (hs : ∀ n,T (n+1)=H-q*T n) :
    ∀ n,q^2*H ≤ T n ∧ T n ≤ H := by
  have he := congrArg (fun x : ℝ => x*H) heq
  intro n
  induction n with
  | zero => rw [h0]; constructor <;> nlinarith [mul_nonneg hq0 (le_of_lt hH)]
  | succ n ih =>
      rw [hs]
      have h1 := mul_nonneg hq0 (show 0 ≤ H-T n by linarith)
      have h2 := mul_nonneg hq0 (show 0 ≤ T n by nlinarith [mul_nonneg (sq_nonneg q) (le_of_lt hH)])
      constructor <;> nlinarith

theorem reference_residual_dominance (q H Klate Kearly Glate Gearly p mu : ℝ)
    (hq : 0<q) (hH : 0<H) (hK : q^2*H ≤ Klate-Kearly)
    (hG : Gearly ≤ Glate) (hmu : mu ≤ p) :
    Kearly+(p-mu)*Gearly<Klate+(p-mu)*Glate := by
  have h1 := mul_nonneg (show 0 ≤ p-mu by linarith) (show 0 ≤ Glate-Gearly by linarith)
  have h2 := mul_pos (sq_pos_of_pos hq) hH
  nlinarith

theorem full_cumulative_residual_propagation (R E : ℕ → ℝ)
    (hs : ∀ n,R (n+1)=R n+E n) (hE : ∀ n,0 ≤ E n) :
    ∀ n,R 0 ≤ R n := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih => rw [hs]; linarith [hE n]

theorem exact_ordinary_window_residual (X Y Gr Gl Pr Pl mu : ℝ)
    (hX : X=Gr-Gl) (hY : Y=Pr-Pl) :
    X-mu*Y=(Gr-mu*Pr)-(Gl-mu*Pl) := by rw [hX,hY]; ring

theorem ordinary_seed_gives_LC (prev cur next a b mu : ℝ)
    (ha : 0<a) (had : a=cur-prev) (hbd : b=next-cur)
    (hmu : b=mu*a) (hseed : 0<cur-mu*prev) :
    0<cur^2-prev*next := by
  have hid : cur^2-prev*next=a*(cur-mu*prev) := by
    have hb' : next-cur=mu*(cur-prev) := by simpa [had,hbd] using hmu
    rw [had]
    have hbp := congrArg (fun x : ℝ => x*prev) hb'
    nlinarith
  rw [hid]
  exact mul_pos ha hseed

theorem first_strict_crossing (xs : List ℕ) (u : ℕ) (h : u<xs.sum) :
    ∃ p d s,xs=p++d::s ∧ p.sum ≤ u ∧ u<p.sum+d := by
  induction xs generalizing u with
  | nil => simp only [List.sum_nil] at h; omega
  | cons a xs ih =>
      by_cases ha : u<a
      · refine ⟨[],a,xs,by simp,by simp,?_⟩
        simpa using ha
      · have hax : a ≤ u := by omega
        have hh : u-a<xs.sum := by simp only [List.sum_cons] at h; omega
        obtain ⟨p,d,s,he,hlo,hhi⟩ := ih (u-a) hh
        refine ⟨a::p,d,s,?_,?_,?_⟩
        · simp [he]
        · simp only [List.sum_cons]; omega
        · simp only [List.sum_cons]; omega

#print axioms crossing_read_guards
#print axioms golden_endpoint_cross
#print axioms strict_subtracted_window_ratio
#print axioms full_alternating_partial_margin
#print axioms reference_residual_dominance
#print axioms full_cumulative_residual_propagation
#print axioms exact_ordinary_window_residual
#print axioms ordinary_seed_gives_LC
#print axioms first_strict_crossing

end UniversalLateCFirstCrossing

