import Mathlib
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

namespace PureTernaryCompleteC

def norm (a b x y : ℝ) := b*x^2+a*x*y+y^2

theorem whole_renewal_residual_norm (a b : ℝ) (E : ℕ → ℝ)
    (h0 : E 0=1) (h1 : E 1= -a)
    (hr : ∀ n,E (n+2)= -b*E n-a*E (n+1)) :
    ∀ n,norm a b (E n) (E (n+1))=b^(n+1) := by
  intro n
  induction n with
  | zero => simp [norm,h0,h1];ring
  | succ n ih =>
      rw [show n+1+1=n+2 by omega,hr]
      dsimp [norm] at ih ⊢
      rw [show n+1+1=n+2 by omega,pow_succ]
      linear_combination b*ih

theorem entire_renewal_residual_unit_bound (a b : ℝ) (E : ℕ → ℝ)
    (hb0 : 1/2 ≤ b) (hb1 : b ≤ 3/5) (ha : a^2 ≤ 3/4)
    (hN : ∀ n,norm a b (E n) (E (n+1))=b^(n+1)) :
    ∀ k,(E (k+3))^2<1 := by
  have hb : 0 ≤ b := by linarith
  have hu : b ≤ 1 := by linarith
  have hpow : ∀ k : ℕ,b^k ≤ 1 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [pow_succ]
        have h := mul_le_mul_of_nonneg_left hu (pow_nonneg hb k)
        nlinarith
  have h2 : b^2 ≤ (3/5:ℝ)^2 := by nlinarith [mul_self_le_mul_self hb hb1]
  have h3 : b^3 ≤ (3/5:ℝ)^3 := by
    have h := mul_le_mul h2 hb1 hb (by norm_num : (0:ℝ) ≤ (3/5:ℝ)^2)
    nlinarith
  intro k
  have hnk := hN (k+2)
  have hid : k+2+1=k+3 := by omega
  rw [hid,pow_add] at hnk
  have hsmall := mul_le_mul_of_nonneg_right (hpow k) (pow_nonneg hb 3)
  simp only [one_mul] at hsmall
  have hx := mul_nonneg (show 0 ≤ b-1/2 by linarith) (sq_nonneg (E (k+2)))
  have hy := mul_nonneg (show 0 ≤ 3/4-a^2 by linarith) (sq_nonneg (E (k+3)))
  have hs := sq_nonneg (E (k+2)/2+a*E (k+3))
  dsimp [norm] at hnk
  nlinarith [sq_nonneg (E (k+2))]

theorem complete_first_physical_minor (P R S A B : ℝ)
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hR : R ≤ 2*P)
    (hM : -P ≤ R^2-P*S) (hB : 4*A+1 ≤ B) :
    0 ≤ (R-A)^2-P*(S-B) := by
  have h1 := mul_nonneg hA (show 0 ≤ 2*P-R by linarith)
  have h2 := mul_nonneg hP (show 0 ≤ B-4*A-1 by linarith)
  nlinarith [sq_nonneg A]

theorem first_source_growth_gap (l R S A B r : ℝ)
    (hl : l ≤ 2) (hA0 : 0 ≤ A) (hA : A ≤ 2)
    (hB : r+2 ≤ B) (hgap : -2 ≤ l*R-S) :
    r-4 ≤ l*(R-A)-(S-B) := by
  have h := mul_nonneg hA0 (show 0 ≤ 2-l by linarith)
  nlinarith

theorem first_cut_startup_minor (P R S c : ℝ)
    (hP : 0 ≤ P) (hR : R ≤ 2*P) (hM : 0 ≤ R^2-P*S)
    (hc : 4 ≤ c) : 0 ≤ (R-1)^2-P*(S-c) := by
  have h := mul_nonneg hP (show 0 ≤ c-4 by linarith)
  nlinarith

theorem second_cut_startup_minor (P R S c e : ℝ)
    (hP : 0 ≤ P) (hS : 0 ≤ S) (hc : 0 ≤ c)
    (hR : R ≤ 2*P) (hM : 0 ≤ R^2-P*S)
    (he : 4*c ≤ e) (hcc : e ≤ c^2) :
    0 ≤ (R-c)^2-(P-1)*(S-e) := by
  have h1 := mul_nonneg hc (show 0 ≤ 2*P-R by linarith)
  have h2 := mul_nonneg hP (show 0 ≤ e-4*c by linarith)
  nlinarith

theorem third_cut_startup_minor (P R S c e f : ℝ)
    (hP : 0 ≤ P) (hS : 0 ≤ S) (hc : 0 ≤ c) (he0 : 0 ≤ e)
    (hR : R ≤ 2*P) (hM : 0 ≤ R^2-P*S)
    (hf : 4*e ≤ f) (hce : c*f ≤ e^2) :
    0 ≤ (R-e)^2-(P-c)*(S-f) := by
  have h1 := mul_nonneg he0 (show 0 ≤ 2*P-R by linarith)
  have h2 := mul_nonneg hP (show 0 ≤ f-4*e by linarith)
  have h3 := mul_nonneg hc hS
  nlinarith

theorem all_startup_source_budgets (r : ℝ) (hr : 18 ≤ r) :
    4 ≤ r ∧ 4*r ≤ r*(r+1)/2 ∧ r*(r+1)/2 ≤ r^2 ∧
    4*(r*(r+1)/2) ≤ r*(r-1)*(r+4)/6 ∧
    r*(r*(r-1)*(r+4)/6) ≤ (r*(r+1)/2)^2 := by
  have h1 := mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ r-7 by linarith)
  have h2 := mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ r-1 by linarith)
  have hp : 0 ≤ r^2-9*r-16 := by nlinarith [sq_nonneg (r-18)]
  have h3 := mul_nonneg (show 0 ≤ r by linarith) hp
  constructor
  · linarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · have hid : (r*(r+1)/2)^2-r*(r*(r-1)*(r+4)/6)=r^2*(r^2+11)/12 := by ring
    have h := mul_nonneg (sq_nonneg r) (show 0 ≤ r^2+11 by positivity)
    nlinarith

theorem true_ordinary_seed (l mu D H K r : ℝ)
    (hr : 18 ≤ r) (hm : mu ≤ l) (hD : D ≤ 2*H)
    (hgap : r-4 ≤ (l-mu)*D) (hK : -1 ≤ K-l*H) :
    6 ≤ K-mu*H := by
  have h := mul_nonneg (show 0 ≤ l-mu by linarith) (show 0 ≤ 2*H-D by linarith)
  nlinarith

theorem finite_double_cumulative_entry_transfer (f g d : ℕ → ℝ) (mu : ℝ) (L : ℕ)
    (hdf : ∀ n,n ≤ L → f (n+1)-f n=d n)
    (hgf : ∀ n,n ≤ L → g (n+1)-g n=f (n+1))
    (hd : ∀ n,n<L → mu*d n ≤ d (n+1))
    (hf0 : mu*f 0 ≤ f 1) (hg0 : mu*g 0 ≤ g 1) :
    ∀ n,n ≤ L → mu*f n ≤ f (n+1) ∧ mu*g n ≤ g (n+1) := by
  intro n
  induction n with
  | zero => intro _;exact ⟨hf0,hg0⟩
  | succ n ih =>
      intro hn
      have hold := ih (by omega)
      have h1 := hdf n (by omega)
      have h2 := hdf (n+1) hn
      have hd1 := hd n (by omega)
      have hfid : (f (n+1+1)-mu*f (n+1))-(f (n+1)-mu*f n)=d (n+1)-mu*d n := by
        linear_combination h2-mu*h1
      have hf : mu*f (n+1) ≤ f (n+1+1) := by linarith [hold.1]
      have hg1 := hgf n (by omega)
      have hg2 := hgf (n+1) hn
      have hgid : (g (n+1+1)-mu*g (n+1))-(g (n+1)-mu*g n)=f (n+1+1)-mu*f (n+1) := by
        linear_combination hg2-mu*hg1
      exact ⟨hf,by linarith [hold.2]⟩

theorem complete_small_count_padding_reduction (r alpha n : ℕ)
    (_hr : 11 ≤ r) (_hu : r ≤ 17) (ha : r ≤ alpha) (hn : n ≤ 2*r) :
    n<alpha+r+1 ∧ n<r+r+1 := by omega

#print axioms whole_renewal_residual_norm
#print axioms entire_renewal_residual_unit_bound
#print axioms complete_first_physical_minor
#print axioms first_source_growth_gap
#print axioms first_cut_startup_minor
#print axioms second_cut_startup_minor
#print axioms third_cut_startup_minor
#print axioms all_startup_source_budgets
#print axioms true_ordinary_seed
#print axioms finite_double_cumulative_entry_transfer
#print axioms complete_small_count_padding_reduction

end PureTernaryCompleteC
