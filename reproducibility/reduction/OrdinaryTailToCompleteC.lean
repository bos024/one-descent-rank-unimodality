import Mathlib
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace OrdinaryTailToCompleteC

theorem ordinary_minor_bounds_slope_tilt (x y z mu : ℝ)
    (hg : 0<y-x) (hmu : mu*(y-x)=z-y) (hLC : x*z ≤ y^2) :
    mu*x ≤ y := by
  have hid : (mu*x-y)*(y-x)=x*z-y^2 := by linear_combination x*hmu
  nlinarith

theorem previous_ordinary_ratio_dominates (x y z mu : ℝ)
    (hx : 0 ≤ x) (hy : 0<y) (hmu : mu*y ≤ z) (hLC : x*z ≤ y^2) :
    mu*x ≤ y := by
  have h := mul_le_mul_of_nonneg_right hmu hx
  nlinarith

theorem whole_prefix_ordinary_tilt (f : ℕ → ℝ) (mu : ℝ) :
    ∀ K : ℕ,(∀ n,n ≤ K+1 → 0<f n) →
      (∀ n,n<K → f n*f (n+2) ≤ (f (n+1))^2) →
      mu*f K ≤ f (K+1) → ∀ n,n ≤ K → mu*f n ≤ f (n+1) := by
  intro K
  induction K with
  | zero =>
      intro _ _ hlast n hn
      have he : n=0 := by omega
      simpa [he] using hlast
  | succ K ih =>
      intro hp hl hlast n hn
      have hprev : mu*f K ≤ f (K+1) :=
        previous_ordinary_ratio_dominates (f K) (f (K+1)) (f (K+2)) mu
          (le_of_lt (hp K (by omega))) (hp (K+1) (by omega)) hlast (hl K (by omega))
      by_cases hh : n ≤ K
      · exact ih (fun j hj => hp j (by omega)) (fun j hj => hl j (by omega)) hprev n hh
      · have he : n=K+1 := by omega
        simpa [he] using hlast

theorem complete_finite_ordinary_to_cumulative_bridge (f g : ℕ → ℝ) (l mu : ℝ) (K : ℕ)
    (hp : ∀ n,n ≤ K+1 → 0<f n)
    (hLC : ∀ n,n ≤ K → f n*f (n+2) ≤ (f (n+1))^2)
    (hentry : f 1 ≤ l*f 0)
    (hslope : 0<f (K+1)-f K)
    (hmu : mu*(f (K+1)-f K)=f (K+2)-f (K+1))
    (hgf : ∀ n,n ≤ K+1 → g (n+1)-g n=f n)
    (hg0 : 0 ≤ g 0) (hgentry : l*g 0 ≤ g 1) :
    mu ≤ l ∧ ∀ n,n ≤ K+1 → mu*g n ≤ g (n+1) := by
  have hlast := ordinary_minor_bounds_slope_tilt (f K) (f (K+1)) (f (K+2)) mu hslope hmu (hLC K (by omega))
  have hf := whole_prefix_ordinary_tilt f mu K hp (fun n hn => hLC n (by omega)) hlast
  have hfirst := hf 0 (by omega)
  have hm : mu ≤ l := by nlinarith [hp 0 (by omega)]
  constructor
  · exact hm
  intro n
  induction n with
  | zero =>
      intro _
      have h := mul_nonneg (show 0 ≤ l-mu by linarith) hg0
      nlinarith
  | succ n ih =>
      intro hn
      have hold := ih (by omega)
      have ht := hf n (by omega)
      have h1 := hgf n (by omega)
      have h2 := hgf (n+1) hn
      have hid : (g (n+1+1)-mu*g (n+1))-(g (n+1)-mu*g n)=f (n+1)-mu*f n := by
        linear_combination h2-mu*h1
      linarith

theorem first_integer_loss_spectral_entry (x y loss l : ℝ)
    (hres : y-l*x<1) (hloss : 1 ≤ loss) : y-loss<l*x := by linarith

#print axioms ordinary_minor_bounds_slope_tilt
#print axioms previous_ordinary_ratio_dominates
#print axioms whole_prefix_ordinary_tilt
#print axioms complete_finite_ordinary_to_cumulative_bridge
#print axioms first_integer_loss_spectral_entry
end OrdinaryTailToCompleteC
