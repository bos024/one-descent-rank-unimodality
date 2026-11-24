import Mathlib

set_option maxHeartbeats 0
namespace RegularizedFibonacciEnvelope

def fi (n : ℕ) : ℤ := Nat.fib n

theorem fi_rec (n : ℕ) : fi (n+2)=fi n+fi (n+1) := by
  unfold fi
  exact_mod_cast (Nat.fib_add_two (n:=n))

theorem cassini (n : ℕ) : fi (n+1)^2-fi n*fi (n+2)=(-1:ℤ)^n := by
  induction n with
  | zero => norm_num [fi]
  | succ n ih =>
    change fi (n+2)^2-fi (n+1)*fi (n+3)=(-1:ℤ)^(n+1)
    have he : fi (n+2)^2-fi (n+1)*fi (n+3)=
        -(fi (n+1)^2-fi n*fi (n+2)) := by
      rw [fi_rec (n+1),fi_rec n]
      ring
    rw [he,ih,pow_succ]
    ring

theorem sign_power_bounds (n : ℕ) : -1 ≤ (-1:ℤ)^n ∧ (-1:ℤ)^n ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ];constructor <;> nlinarith [ih.1,ih.2]

theorem positive_fibonacci (n : ℕ) (hn : 1 ≤ n) : 1 ≤ fi n := by
  have hh : 0 < Nat.fib n := Nat.fib_pos.mpr (by omega)
  have hh2 : 1 ≤ Nat.fib n := by omega
  unfold fi
  exact_mod_cast hh2

theorem regularized_ratio_identity (a b c d e : ℤ)
    (hc : c=a+b) (hd : d=b+c) (he : e=c+d) :
    b*(e-1)-c*(d-1)=a-(c^2-b*d) := by
  rw [he,hd,hc]
  ring

theorem fibonacci_regularization_density (n : ℕ) :
    fi (n+2)*(fi (n+3)-1) ≤ fi (n+1)*(fi (n+4)-1) := by
  have hid := regularized_ratio_identity (fi n) (fi (n+1))
    (fi (n+2)) (fi (n+3)) (fi (n+4)) (fi_rec n) (fi_rec (n+1)) (fi_rec (n+2))
  rw [cassini (n+1)] at hid
  cases n with
  | zero => norm_num [fi]
  | succ n =>
    have hf := positive_fibonacci (n+1) (by omega)
    have hs := sign_power_bounds (n+2)
    nlinarith [hs.2]

theorem regularized_lc_identity (a b c delta : ℤ)
    (hc : c=a+b) (hd : 2*b-a=delta) :
    (a-1)^2-(b-1)*(c-1)=a^2-b*c+delta := by
  rw [hc] at *
  nlinarith

theorem doubled_fib_difference (n : ℕ) : 2*fi (n+3)-fi (n+4)=fi (n+1) := by
  rw [fi_rec (n+2),fi_rec (n+1)]
  ring

theorem regularized_fibonacci_lc (n : ℕ) :
    0 ≤ (fi (n+4)-1)^2-(fi (n+3)-1)*(fi (n+5)-1) := by
  have hid := regularized_lc_identity (fi (n+4)) (fi (n+3)) (fi (n+5))
    (fi (n+1)) (by rw [fi_rec (n+3)];ring) (doubled_fib_difference n)
  have hc := cassini (n+3)
  have he : (-1:ℤ)^(n+3)=(-1:ℤ)^(n+1) := by
    have hn : n+3=(n+1)+2 := by omega
    rw [hn,pow_add]
    norm_num
  rw [he] at hc
  have hp := positive_fibonacci (n+1) (by omega)
  have hs := sign_power_bounds (n+1)
  nlinarith [hs.1]

theorem regularized_fibonacci_doubling (n : ℕ) :
    fi (n+4)-1 ≤ 2*(fi (n+3)-1) := by
  have hh := doubled_fib_difference n
  have hp := positive_fibonacci (n+1) (by omega)
  omega

theorem one_regularization_counter : (2:ℤ)*2-1*3=1 ∧ (0:ℤ)<1 := by norm_num

theorem zero_regularization_counter :
    (75003:ℤ)*46367-46354*75024=1605 ∧ (0:ℤ)<1605 := by norm_num

#print axioms fi_rec
#print axioms cassini
#print axioms sign_power_bounds
#print axioms positive_fibonacci
#print axioms regularized_ratio_identity
#print axioms fibonacci_regularization_density
#print axioms regularized_lc_identity
#print axioms doubled_fib_difference
#print axioms regularized_fibonacci_lc
#print axioms regularized_fibonacci_doubling
#print axioms one_regularization_counter
#print axioms zero_regularization_counter
end RegularizedFibonacciEnvelope
