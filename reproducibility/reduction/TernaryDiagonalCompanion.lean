import Mathlib
set_option maxHeartbeats 1000000

namespace TernaryDiagonalCompanion

theorem exact_positive_diagonal_recurrence {R : Type*} [CommRing R]
    (s2 s3 z3 b p f : R) (hrel : s3-s2=z3) (hsum : (1-s3)*b=1-p) :
    1+s3+s3^2*b+s3^2*p*(1+s2*f)
      =s2*s3^2*(b+p*f)+(1+s3+s3^2+z3*s3^2*b) := by
  have hp : p=1-(1-s3)*b := by linear_combination hsum
  rw [hp,← hrel]
  ring

theorem exact_positive_defect_recurrence {R : Type*} [CommRing R]
    (s2 s3 z3 b p H : R) (hrel : s3-s2=z3)
    (hsum : (1-s3)*b=1-p) (hH : (1-s3)*H=1) :
    H*(1-s2*s3^2)-(1+s3+s3^2+z3*s3^2*b)=z3*s3^2*p*H := by
  have hp : p=1-(1-s3)*b := by linear_combination hsum
  have hid : 1-s2*s3^2
      =(1-s3)*(1+s3+s3^2+z3*s3^2*b)+z3*s3^2*p := by
    rw [hp,← hrel]
    ring
  rw [hid]
  calc
    H*((1-s3)*(1+s3+s3^2+z3*s3^2*b)+z3*s3^2*p)
        -(1+s3+s3^2+z3*s3^2*b)
      =((1-s3)*H-1)*(1+s3+s3^2+z3*s3^2*b)+z3*s3^2*p*H := by ring
    _=z3*s3^2*p*H := by rw [hH]; ring

theorem exact_positive_derivative_defect_source {R : Type*} [CommRing R]
    (z p H d : R) (hD : (1-z)*H=1+z^2*d) :
    z^3*p*(1-z)*H=z^2*(z*p+z^3*p*d) := by
  calc
    z^3*p*(1-z)*H=z^3*p*((1-z)*H) := by ring
    _=z^3*p*(1+z^2*d) := by rw [hD]
    _=z^2*(z*p+z^3*p*d) := by ring

#print axioms exact_positive_diagonal_recurrence
#print axioms exact_positive_defect_recurrence
#print axioms exact_positive_derivative_defect_source

end TernaryDiagonalCompanion
