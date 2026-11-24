import Mathlib
set_option maxHeartbeats 2000000
namespace BinaryTernaryA2SourceCone

theorem small_missing_reflection_dichotomy (r k alpha H : ℕ)
    (hk : 3 ≤ k) (hK : k ≤ 4) (ha : 1 ≤ alpha) (hH : 2*r+2 ≤ H) :
    2*r+k ≤ alpha+H ∨
    (k=4 ∧ alpha=1 ∧ H=2*r+2 ∧ r+(r+k-1)=alpha+H) := by omega

theorem exceptional_curvature_payment (r C d q : ℝ)
    (hr : 0 ≤ r) (hC : 0 ≤ C) (hbound : (r+1)*C ≤ d) (hq : d ≤ q) :
    C ≤ q := by
  have hh := mul_nonneg hr hC
  nlinarith

theorem negative_rank_compulsory_birth (a k : ℕ)
    (ha : 3 ≤ a) (hk : 3 ≤ k) (hK : k ≤ 4) :
    1 ≤ a+2-k ∧ a+2-k ≤ a-1 := by omega

theorem complementary_half_tail_guards (D n j : ℕ)
    (h : n+j=D) (hj : D+2<2*j) : 2*n ≤ D := by omega

def UpDown (f : ℕ → ℝ) (l : ℕ) : Prop :=
  (∀ n, n<l → f n ≤ f (n+1)) ∧ (∀ n, l ≤ n → f (n+1) ≤ f n)

theorem complete_positive_source_splice (E : ℕ → ℝ) (M l : ℕ)
    (_hl : l ≤ M)
    (hup : ∀ n, n<l → E n ≤ E (n+1))
    (hdown : ∀ n, l ≤ n → n<M → E (n+1) ≤ E n)
    (htail : ∀ n, M ≤ n → 0 ≤ E n → E (n+1) ≤ E n)
    (hnorecover : ∀ i j, E i<0 → i<j → E j ≤ 0) :
    UpDown (fun n => max 0 (E n)) l := by
  constructor
  · intro n hn
    exact max_le_max_left 0 (hup n hn)
  · intro n hn
    by_cases hM : n<M
    · exact max_le_max_left 0 (hdown n hn hM)
    · by_cases hp : 0 ≤ E n
      · exact max_le_max_left 0 (htail n (by omega) hp)
      · have hnext : E (n+1) ≤ 0 := hnorecover n (n+1) (by linarith) (by omega)
        change max 0 (E (n+1)) ≤ max 0 (E n)
        rw [max_eq_left hnext, max_eq_left (by linarith : E n ≤ 0)]

theorem positive_source_no_holes (P : ℕ → ℝ) (l : ℕ)
    (hUI : UpDown P l) (h0 : 0<P 0) (hpos : ∀ n, 0 ≤ P n) :
    ∀ i j, P i=0 → i<j → P j=0 := by
  have hpre : ∀ n, n ≤ l → P 0 ≤ P n := by
    intro n
    induction n with
    | zero => intro _; exact le_rfl
    | succ n ih =>
        intro hn
        exact le_trans (ih (by omega)) (hUI.1 n (by omega))
  have hpost : ∀ i k, l ≤ i → P (i+k) ≤ P i := by
    intro i k hi
    induction k with
    | zero => simp
    | succ k ih =>
        have he := hUI.2 (i+k) (by omega)
        simpa [Nat.add_assoc] using le_trans he ih
  intro i j hz hij
  have hi : l ≤ i := by
    by_contra hh
    have he := hpre i (by omega)
    rw [hz] at he
    linarith
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (show i ≤ j by omega)
  have he : P j ≤ P i := by rw [hk]; exact hpost i k hi
  rw [hz] at he
  exact le_antisymm he (hpos j)

def back (p : ℕ → ℝ) (n : ℕ) : ℝ := if n=0 then 0 else p (n-1)

theorem exact_raw_source_weighted_difference (p : ℕ → ℝ) (n : ℕ) :
    (2:ℝ)^(n+1)*(p (n+1)-back p (n+1))-
      2^n*(p n-back p n) =
    2^n*((2*p (n+1)-back p (n+1))-(2*p n-back p n)) := by
  have hb : back p (n+1)=p n := by simp [back]
  rw [hb, pow_succ]
  ring

theorem weighted_difference_sign_transfer (E W : ℕ → ℝ) (n : ℕ)
    (h : W (n+1)-W n=(2:ℝ)^n*(E (n+1)-E n)) :
    (W n ≤ W (n+1) ↔ E n ≤ E (n+1)) ∧
    (W (n+1) ≤ W n ↔ E (n+1) ≤ E n) := by
  have hp : 0<(2:ℝ)^n := by positivity
  constructor <;> constructor <;> intro hh <;> nlinarith

theorem entire_mode_plateau_source_join (pmax Efirst Eplateau Eout : ℝ)
    (hfirst : pmax ≤ Efirst) (hplateau : Eplateau=pmax)
    (hout : Eout ≤ pmax) : Eplateau ≤ Efirst ∧ Eout ≤ Eplateau := by
  constructor <;> linarith

theorem append_source_excluded_on_entire_rising_prefix (a sigma i : ℕ)
    (hs : sigma<a) (hi : i ≤ sigma) : i<a ∧ i<a+1 := by omega

#print axioms small_missing_reflection_dichotomy
#print axioms exceptional_curvature_payment
#print axioms negative_rank_compulsory_birth
#print axioms complementary_half_tail_guards
#print axioms complete_positive_source_splice
#print axioms positive_source_no_holes
#print axioms exact_raw_source_weighted_difference
#print axioms weighted_difference_sign_transfer
#print axioms entire_mode_plateau_source_join
#print axioms append_source_excluded_on_entire_rising_prefix
end BinaryTernaryA2SourceCone
