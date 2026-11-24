import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace TernaryRichCompleteC

theorem exterior_square_tribonacci_identity (A B C : ℝ) :
    (A+2*B+2*C)^2-(A+B+C)*(2*A+3*B+4*C)
    =-((A+B+C)^2-C*(A+2*B+2*C))
      -(C^2-B*(A+B+C))+(B^2-A*C) := by ring

theorem signed_third_order_majorant (R M : ℕ → ℝ)
    (hR : ∀ n,R (n+3)=R n+R (n+1)+R (n+2))
    (hM : ∀ n,M (n+3)= -M (n+2)-M (n+1)+M n)
    (hbase : ∀ n,n<3 → -R n ≤ M n ∧ M n ≤ R n) :
    ∀ n,-R n ≤ M n ∧ M n ≤ R n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n<3
      · exact hbase n hn
      · have h0 := ih (n-3) (by omega)
        have h1 := ih (n-2) (by omega)
        have h2 := ih (n-1) (by omega)
        have hrr := hR (n-3)
        have hmm := hM (n-3)
        have e0 : n-3+3=n := by omega
        have e1 : n-3+1=n-2 := by omega
        have e2 : n-3+2=n-1 := by omega
        rw [e0,e1,e2] at hrr hmm
        constructor <;> linarith

def minor (R : ℕ → ℝ) (n : ℕ) : ℝ := R (n+1)^2-R n*R (n+2)

theorem full_tribonacci_minor_recurrence (R : ℕ → ℝ)
    (hR : ∀ n,R (n+3)=R n+R (n+1)+R (n+2)) :
    ∀ n,minor R (n+3)= -minor R (n+2)-minor R (n+1)+minor R n := by
  intro n
  have h3 := hR n
  have h4 : R (n+4)=R (n+1)+R (n+2)+R (n+3) := by
    simpa [Nat.add_assoc] using hR (n+1)
  have h5 : R (n+5)=R (n+2)+R (n+3)+R (n+4) := by
    simpa [Nat.add_assoc] using hR (n+2)
  norm_num only [minor,Nat.add_assoc]
  simp only [h5,h4,h3]
  ring

theorem universal_tribonacci_previous_minor_bound (R : ℕ → ℝ)
    (h0 : R 0=1) (h1 : R 1=2) (h2 : R 2=3)
    (hR : ∀ n,R (n+3)=R n+R (n+1)+R (n+2)) :
    ∀ n,2 ≤ n → -R n ≤ minor R n ∧ minor R n ≤ R n := by
  have h3 : R 3=6 := by
    have h := hR 0
    norm_num [h0,h1,h2] at h
    exact h
  have h4 : R 4=11 := by
    have h := hR 1
    norm_num [h1,h2,h3] at h
    exact h
  have h5 : R 5=20 := by
    have h := hR 2
    norm_num [h2,h3,h4] at h
    exact h
  have h6 : R 6=37 := by
    have h := hR 3
    norm_num [h3,h4,h5] at h
    exact h
  let T : ℕ → ℝ := fun n => R (n+2)
  let M : ℕ → ℝ := fun n => minor R (n+2)
  have hT : ∀ n,T (n+3)=T n+T (n+1)+T (n+2) := by
    intro n
    dsimp [T]
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hR (n+2)
  have hM : ∀ n,M (n+3)= -M (n+2)-M (n+1)+M n := by
    intro n
    dsimp [M]
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using full_tribonacci_minor_recurrence R hR (n+2)
  have hbase : ∀ n,n<3 → -T n ≤ M n ∧ M n ≤ T n := by
    intro n hn
    interval_cases n <;> norm_num [T,M,minor,h2,h3,h4,h5,h6]
  have hbound := signed_third_order_majorant T M hT hM hbase
  intro n hn
  have h := hbound (n-2)
  have he : n-2+2=n := by omega
  simpa [T,M,he] using h

theorem central_integer_budget_implies_relative_LC (A P B R S T : ℝ)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hdom : A ≤ R)
    (hM : A ≤ A^2-P*B) (hRef : R^2-S*T ≤ R) :
    P*B*R^2 ≤ A^2*S*T := by
  have hp := mul_nonneg hA (show 0 ≤ R-A by linarith)
  have hpa : 0 ≤ A^2 := sq_nonneg A
  have hpr : 0 ≤ R^2 := sq_nonneg R
  have h1 := mul_nonneg (show 0 ≤ A^2-P*B-A by linarith) hpr
  have h2 := mul_nonneg (show 0 ≤ R-(R^2-S*T) by linarith) hpa
  have h3 := mul_nonneg hp hR
  nlinarith

theorem first_ternary_loss_minor_budget (r e T U V : ℝ)
    (hr : 6 ≤ r) (he : 0 ≤ e) (hT : 0 ≤ T)
    (hU : U ≤ 2*T) (hM : -T ≤ U^2-T*V) :
    U-1 ≤ (U-1)^2-T*(V-(r+1+e)) := by
  have hp := mul_nonneg (show 0 ≤ r-6+e by linarith) hT
  nlinarith

theorem second_ternary_loss_minor_budget (r U V W : ℝ)
    (hr : 7 ≤ r) (hU : 0 ≤ U) (hV : V ≤ 2*U)
    (hM : -V ≤ V^2-U*W)
    (hnext : (r^2+3*r+6)/2 ≤ W) :
    V-(r+1) ≤ (V-(r+1))^2-(U-1)*(W-(r^2+3*r+6)/2) := by
  have hpoly : 0 ≤ (r^2+3*r+6)/2-4*(r+1)-4 := by nlinarith
  have hp := mul_nonneg hU hpoly
  have hid :
      ((V-(r+1))^2-(U-1)*(W-(r^2+3*r+6)/2))-(V-(r+1))
      =(V^2-U*W)+(r+1)^2+(r+1)-(2*(r+1)+1)*V
        +U*((r^2+3*r+6)/2)+(W-(r^2+3*r+6)/2) := by ring
  have hp2 := mul_nonneg (show 0 ≤ 2*(r+1)+2 by linarith)
    (show 0 ≤ 2*U-V by linarith)
  nlinarith [sq_nonneg (r+1)]

theorem strict_integer_concavity_minor_budget (A B C : ℝ)
    (hA : 0 ≤ A) (hgain : 1 ≤ B-A) (hcurve : 1 ≤ 2*B-A-C) :
    B ≤ B^2-A*C := by
  have h1 := mul_nonneg hA (show 0 ≤ 2*B-A-C-1 by linarith)
  have h2 := mul_nonneg (show 0 ≤ B-A by linarith) (show 0 ≤ B-A-1 by linarith)
  nlinarith

theorem positive_three_window_minor_budget (a b c d e : ℝ)
    (ha : 0 ≤ a) (hb : 0<b) (hc : 0<c) (hd : 0 ≤ d)
    (h1 : b ≤ b^2-a*c) (h2 : 0 ≤ c^2-b*d) (h3 : d ≤ d^2-c*e) :
    b+c+d ≤ (b+c+d)^2-(a+b+c)*(c+d+e) := by
  have hm1 : 0 ≤ b^2-a*c := by linarith
  have hm3 : 0 ≤ d^2-c*e := by linarith
  have hc1 : c ≤ b*c-a*d := by
    have hid : b*(b*c-a*d-c)=c*(b^2-a*c-b)+a*(c^2-b*d) := by ring
    have hleft := mul_nonneg (le_of_lt hc) (show 0 ≤ b^2-a*c-b by linarith)
    have hright := mul_nonneg ha h2
    nlinarith
  have hc2 : 0 ≤ c*d-b*e := by
    have hid : c*(c*d-b*e)=d*(c^2-b*d)+b*(d^2-c*e) := by ring
    have hleft := mul_nonneg hd h2
    have hright := mul_nonneg (le_of_lt hb) hm3
    nlinarith
  have hc3 : 0 ≤ b*d-a*e := by
    have hid : b*(b*d-a*e)=d*(b^2-a*c)+a*(c*d-b*e) := by ring
    have hleft := mul_nonneg hd hm1
    have hright := mul_nonneg ha hc2
    nlinarith
  have hid : (b+c+d)^2-(a+b+c)*(c+d+e)
      =(b^2-a*c)+(d^2-c*e)+(b*c-a*d)+(c*d-b*e)+(b*d-a*e) := by ring
  linarith

theorem exact_all_padding_clamp (u r : ℕ) :
    r+u+(r+u/2)+1=(3*u+4*r)/2+1 := by omega

theorem later_three_window_old_minor_reads (r n ell : ℕ)
    (hr : 8 ≤ r) (hn : r+6 ≤ n) (he : n ≤ ell) :
    r+3 ≤ n-3 ∧ n-1<ell ∧ 2 ≤ n-4 := by omega

theorem strict_mode_transition_read_guards (r n ell e R : ℕ)
    (hr : 8 ≤ r) (hn : r+6 ≤ n) (hafter : ell+1 ≤ n)
    (hnew : n<e) (hwindow : e ≤ ell+3) (hsupport : e ≤ R+1) :
    11 ≤ n-3 ∧ n-3<ell ∧ n ≤ R ∧ n+1 ≤ R+1 := by omega

#print axioms exterior_square_tribonacci_identity
#print axioms signed_third_order_majorant
#print axioms full_tribonacci_minor_recurrence
#print axioms universal_tribonacci_previous_minor_bound
#print axioms central_integer_budget_implies_relative_LC
#print axioms first_ternary_loss_minor_budget
#print axioms second_ternary_loss_minor_budget
#print axioms strict_integer_concavity_minor_budget
#print axioms positive_three_window_minor_budget
#print axioms exact_all_padding_clamp
#print axioms later_three_window_old_minor_reads
#print axioms strict_mode_transition_read_guards

end TernaryRichCompleteC
