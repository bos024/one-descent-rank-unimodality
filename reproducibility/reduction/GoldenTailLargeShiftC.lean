import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace GoldenTailLargeShiftC

theorem monotone_divided_head (E f : ℕ → ℝ) (K : ℕ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q < 1)
    (hE : ∀ n, n ≤ K → 0 < E n)
    (hm : ∀ n, n < K → E n ≤ E (n+1))
    (hbase : f 0=E 0) (hrec : ∀ n, n < K → f (n+1)=E (n+1)-q*f n) :
    ∀ n, n ≤ K → 0 < f n ∧ f n ≤ E n ∧ (1-q)*E n ≤ f n := by
  intro n
  induction n with
  | zero =>
    intro hn
    have hpos := hE 0 hn
    have hh := mul_nonneg hq0 (le_of_lt hpos)
    rw [hbase]
    exact ⟨hpos,le_refl _,by nlinarith only [hh]⟩
  | succ n ih =>
    intro hn
    have hnp : n ≤ K := by omega
    have hlt : n < K := by omega
    obtain ⟨hfp,hfu,hfl⟩ := ih hnp
    have hmono := hm n hlt
    have hcur := hE (n+1) hn
    have h1 := mul_nonneg hq0 (show 0 ≤ E (n+1)-f n by linarith only [hfu,hmono])
    have h2 := mul_nonneg hq0 (le_of_lt hfp)
    have h3 := mul_pos (show 0 < 1-q by linarith only [hq]) hcur
    have hdef := hrec n hlt
    constructor
    · nlinarith only [h1,h3,hdef]
    constructor <;> nlinarith only [h1,h2,hdef]

theorem crossing_entry_parity (h u : ℕ) (hu : u < h) :
    (-1:ℝ)^(h+u)*(-1:ℝ)^(h-u-1) = -1 := by
  rw [← pow_add]
  have heq : h+u+(h-u-1)=2*(h-1)+1 := by omega
  rw [heq,pow_add,pow_mul]
  norm_num

theorem midpoint_entry_geometry (h u : ℝ) (hh : h ≤ 3*u+2) :
    2*(h-u-1) ≤ h+u := by linarith only [hh]

theorem helpful_signed_spectral_entry (f atom J : ℝ)
    (hf : 0 < f) (ha : atom ≤ 0) (hJ : J=f-atom) : 0 < J := by
  linarith only [hf,ha,hJ]

theorem geometric_inverse_entry (q prev cur J : ℝ)
    (hq : q^2+q=1) (hr : prev=q*(cur+J)) :
    (1+q)*prev-cur=J := by
  rw [hr]
  calc
    (1+q)*(q*(cur+J))-cur=(q^2+q)*(cur+J)-cur := by ring
    _=J := by rw [hq]; ring

theorem finite_density_golden_transfer (infprev infcur prev cur p : ℝ)
    (hi : 0 < infprev) (hp : 0 < prev)
    (hg : infcur < p*infprev) (hlr : cur*infprev ≤ prev*infcur) :
    cur < p*prev := by
  have h1 := mul_pos hp (show 0 < p*infprev-infcur by linarith only [hg])
  have hh : 0 < infprev*(p*prev-cur) := by nlinarith only [h1,hlr]
  have hres := (mul_pos_iff_of_pos_left hi).mp hh
  linarith only [hres]

theorem LC_growth_ceiling_step (prev cur next p : ℝ)
    (hp : 0 < prev) (hc : 0 ≤ cur)
    (hlc : prev*next ≤ cur^2) (hg : cur ≤ p*prev) :
    next ≤ p*cur := by
  have h1 := mul_nonneg hc (show 0 ≤ p*prev-cur by linarith only [hg])
  have hh : 0 ≤ prev*(p*cur-next) := by nlinarith only [h1,hlc]
  have hres := (mul_nonneg_iff_of_pos_left hp).mp hh
  linarith only [hres]

theorem golden_large_shift_C_paid (Gprev Gcur Dprev Dcur p : ℝ)
    (hG : 0 ≤ Gprev) (hD : 0 < Dprev)
    (hg : p*Gprev < Gcur) (hd : Dcur < p*Dprev) :
    0 < Gcur*Dprev-Gprev*Dcur := by
  have h1 := mul_pos hD (show 0 < Gcur-p*Gprev by linarith only [hg])
  have h2 := mul_nonneg hG (show 0 ≤ p*Dprev-Dcur by linarith only [hd])
  nlinarith only [h1,h2]

theorem source_band_read_domain (j w k r : ℤ)
    (hj : j ≤ w+k) (hr : k ≤ r) : j+1-r ≤ w+1 := by omega

#print axioms monotone_divided_head
#print axioms crossing_entry_parity
#print axioms midpoint_entry_geometry
#print axioms helpful_signed_spectral_entry
#print axioms geometric_inverse_entry
#print axioms finite_density_golden_transfer
#print axioms LC_growth_ceiling_step
#print axioms golden_large_shift_C_paid
#print axioms source_band_read_domain
end GoldenTailLargeShiftC
