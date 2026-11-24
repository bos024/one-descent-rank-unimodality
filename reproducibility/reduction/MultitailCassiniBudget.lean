import Mathlib

namespace MultitailCassiniBudget

def fib (n : ℕ) : ℤ := Nat.fib n

private theorem fib_rec (n : ℕ) : fib (n+2)=fib n+fib (n+1) := by
  dsimp [fib]
  exact_mod_cast Nat.fib_add_two (n:=n)

private theorem fib_nonneg (n : ℕ) : 0 ≤ fib n := by
  dsimp [fib]
  positivity

private theorem fib_ge_one (n : ℕ) (hn : 1 ≤ n) : 1 ≤ fib n := by
  have hp : 0 < Nat.fib n := Nat.fib_pos.mpr (by omega)
  dsimp [fib]
  omega

def factor (t : ℕ) : ℤ := fib (t-1)+fib (t+1)-1-(-1)^t

theorem all_capacity_Cassini_factor_bound (t : ℕ) (ht : 2 ≤ t) :
    1 ≤ factor t ∧ factor t ≤ fib (t+2)-1 := by
  have hlo : (-1:ℤ)^t ≤ 1 := by
    exact (abs_le.mp (by simp : |(-1:ℤ)^t| ≤ 1)).2
  have hhi : -1 ≤ (-1:ℤ)^t := by
    exact (abs_le.mp (by simp : |(-1:ℤ)^t| ≤ 1)).1
  by_cases htwo : t=2
  · subst t
    norm_num [factor,fib,Nat.fib]
  have ht3 : 3 ≤ t := by omega
  have hp := fib_ge_one (t-2) (by omega)
  have hf1 := fib_rec (t-2)
  have hf2 := fib_rec (t-1)
  have hf3 := fib_rec t
  have ei1 : t-2+2=t := by omega
  have ei2 : t-2+1=t-1 := by omega
  have ei3 : t-1+2=t+1 := by omega
  have ei4 : t-1+1=t := by omega
  rw [ei1,ei2] at hf1
  rw [ei3,ei4] at hf2
  have hm : 1 ≤ fib (t-1) := fib_ge_one _ (by omega)
  have hplus : 3 ≤ fib (t+1) := by
    have hm3 : Nat.fib 4 ≤ Nat.fib (t+1) := Nat.fib_mono (by omega)
    have heq : Nat.fib 4=3 := by decide
    rw [heq] at hm3
    change (3:ℤ) ≤ (Nat.fib (t+1):ℤ)
    exact_mod_cast hm3
  dsimp [factor]
  constructor <;> omega

theorem full_Fibonacci_window_identity (a b : ℤ) (t : ℕ) :
    (∑ j ∈ Finset.range t, (fib (j+1)*a+fib j*b)) =
      (fib (t+2)-1)*a+(fib (t+1)-1)*b := by
  induction t with
  | zero => norm_num [fib,Nat.fib]
  | succ t ih =>
    rw [Finset.sum_range_succ,ih]
    have hf1 := fib_rec t
    have hf2 := fib_rec (t+1)
    have ei1 : t+1+2=t+3 := by omega
    have ei2 : t+1+1=t+2 := by omega
    rw [ei1,ei2] at hf2
    have ei3 : t+1+2=t+3 := by omega
    have ei4 : t+1+1=t+2 := by omega
    simp only [ei3,ei4]
    rw [hf2,hf1]
    ring

structure State where
  a : ℤ
  b : ℤ
  amplitude : ℤ

def step (t : ℕ) (s : State) : State :=
  ⟨(fib (t+2)-1)*s.a+(fib (t+1)-1)*s.b,
   (fib (t+1)-1)*s.a+fib t*s.b,
   factor t*s.amplitude⟩

def state : List ℕ → State
  | [] => ⟨1,0,1⟩
  | t::V => step t (state V)

private theorem cassini (n : ℕ) :
    fib (n+1)^2-fib n*fib (n+2)=(-1:ℤ)^n := by
  induction n with
  | zero => norm_num [fib]
  | succ n ih =>
    change fib (n+2)^2-fib (n+1)*fib (n+3)=(-1:ℤ)^(n+1)
    have he : fib (n+2)^2-fib (n+1)*fib (n+3)=
        -(fib (n+1)^2-fib n*fib (n+2)) := by
      rw [fib_rec (n+1),fib_rec n]
      ring
    rw [he,ih,pow_succ]
    ring

private theorem factor_det (t : ℕ) (ht : 2 ≤ t) :
    fib t^2+fib t*(fib (t+1)-1)-(fib (t+1)-1)^2=factor t := by
  have hc := cassini t
  have hf1 := fib_rec (t-1)
  have ei1 : t-1+2=t+1 := by omega
  have ei2 : t-1+1=t := by omega
  rw [ei1,ei2] at hf1
  rw [fib_rec t] at hc
  dsimp [factor]
  nlinarith only [hc,hf1]

private theorem step_minor (t : ℕ) (ht : 2 ≤ t) (s : State) :
    (step t s).a^2-(step t s).b*((step t s).a+(step t s).b)=
       factor t*(s.a^2-s.b*(s.a+s.b)) := by
  calc
    _ = (fib t^2+fib t*(fib (t+1)-1)-(fib (t+1)-1)^2)*
          (s.a^2-s.b*(s.a+s.b)) := by
      dsimp [step]
      rw [fib_rec t]
      ring
    _ = _ := by rw [factor_det t ht]

theorem all_word_exact_Cassini_amplitude (V : List ℕ)
    (hV : ∀ t ∈ V, 2 ≤ t) :
    (state V).a^2-(state V).b*((state V).a+(state V).b)=
      (state V).amplitude := by
  induction V with
  | nil => norm_num [state]
  | cons t V ih =>
    have ht : 2 ≤ t := hV t (by simp)
    have htail : ∀ j ∈ V, 2 ≤ j := by
      intro j hj
      exact hV j (by simp [hj])
    change (step t (state V)).a^2-
      (step t (state V)).b*((step t (state V)).a+(step t (state V)).b)=_
    rw [step_minor t ht (state V),ih htail]
    rfl

theorem all_word_reference_Cassini_budget (V : List ℕ)
    (hV : ∀ t ∈ V, 2 ≤ t) :
    1 ≤ (state V).amplitude ∧
    (state V).amplitude ≤ (state V).a ∧ 0 ≤ (state V).b ∧
    (V ≠ [] → 1 ≤ (state V).b) := by
  induction V with
  | nil => simp [state]
  | cons t V ih =>
    have ht : 2 ≤ t := hV t (by simp)
    have htail : ∀ j ∈ V, 2 ≤ j := by
      intro j hj
      exact hV j (by simp [hj])
    rcases ih htail with ⟨hA,ha,hb,_⟩
    rcases all_capacity_Cassini_factor_bound t ht with ⟨hc,hcf⟩
    have hp1 := fib_ge_one (t+2) (by omega)
    have hp2 := fib_ge_one (t+1) (by omega)
    have hp3 := fib_ge_one t (by omega)
    have hp4 : 2 ≤ fib (t+1) := by
      have hm : Nat.fib 3 ≤ Nat.fib (t+1) := Nat.fib_mono (by omega)
      have heq : Nat.fib 3=2 := by decide
      rw [heq] at hm
      change (2:ℤ) ≤ (Nat.fib (t+1):ℤ)
      exact_mod_cast hm
    have ha0 : 0 ≤ (state V).a := by omega
    have hca := mul_le_mul_of_nonneg_right hcf ha0
    have hAb := mul_nonneg (show 0 ≤ fib (t+1)-1 by omega) hb
    have hAt := mul_le_mul_of_nonneg_left ha (show 0 ≤ factor t by omega)
    have hprod : 1 ≤ factor t*(state V).amplitude := by nlinarith only [hc,hA]
    have hba := mul_le_mul_of_nonneg_right (show 1 ≤ fib (t+1)-1 by omega) ha0
    have hbb := mul_nonneg (show 0 ≤ fib t by omega) hb
    dsimp [state,step]
    constructor
    · exact hprod
    constructor
    · nlinarith only [hca,hAb,hAt]
    constructor
    · nlinarith only [hba,hbb,ha,hA]
    · intro _
      nlinarith only [hba,hbb,ha,hA]

theorem nonempty_word_two_step_strict_budget (V : List ℕ)
    (hV : ∀ t ∈ V, 2 ≤ t) (hne : V ≠ []) :
    2*(state V).amplitude+1 ≤ 2*(state V).a+(state V).b := by
  rcases all_word_reference_Cassini_budget V hV with ⟨_,ha,_,hb⟩
  have hpos := hb hne
  omega

theorem first_defect_strict_LC_payment (a b c A delta x : ℤ)
    (hA : 0 ≤ A) (ha : 2*A+1 ≤ a)
    (hCassini : -A ≤ b^2-a*c) (hdelta : 1 ≤ delta)
    (hx : x ≤ c-delta) :
    A+1 ≤ b^2-a*x := by
  have ha0 : 0 ≤ a := by omega
  have hm := mul_le_mul_of_nonneg_left hx ha0
  have hd := mul_le_mul_of_nonneg_left hdelta ha0
  nlinarith only [hCassini,hm,hd,ha]

#print axioms all_capacity_Cassini_factor_bound
#print axioms full_Fibonacci_window_identity
#print axioms all_word_exact_Cassini_amplitude
#print axioms all_word_reference_Cassini_budget
#print axioms nonempty_word_two_step_strict_budget
#print axioms first_defect_strict_LC_payment

end MultitailCassiniBudget
