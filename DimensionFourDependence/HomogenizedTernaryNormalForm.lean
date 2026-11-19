import DimensionFourDependence.HomogenizedParameterPencil
import DimensionFourDependence.LastCoordinateDehomogenization

/-! # The polynomial parameters of Proposition 6.6 -/

namespace DimensionFourDependence.TernaryNormalForm

open MvPolynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "t" => (X (Fin.last 3))

noncomputable def quadratic4 : R₄ := t * X 1 + X 0 ^ 2

/-- The homogeneous numerator `t^(2m) P((ty+x²)/t²)`. -/
noncomputable def numerator4 (P : Polynomial K) : R₄ :=
  homogeneousParameterPolynomialValue P P.natDegree quadratic4 (t ^ 2)

/-- The parameter `q` in (6.12), given by a polynomial expression. -/
noncomputable def q4 (P : Polynomial K) (d : ℕ) : R₄ :=
  t ^ (d - 1 - 2 * P.natDegree) * numerator4 P

/-- The parameter `R` in (6.12), given by a polynomial expression. -/
noncomputable def correction4 (P : Polynomial K) (d : ℕ) : R₄ :=
  t ^ (d - 4 * P.natDegree) * numerator4 P ^ 2

theorem q4_correction4_square_identity (P : Polynomial K) {d : ℕ}
    (hm : 0 < P.natDegree) (hd : 4 * P.natDegree ≤ d) :
    (t : R₄) ^ (d - 1) * correction4 P d = t * q4 P d ^ 2 := by
  unfold correction4 q4
  rw [mul_pow]
  calc
    _ = t ^ ((d - 1) + (d - 4 * P.natDegree)) * numerator4 P ^ 2 := by
      rw [pow_add]; ring
    _ = t ^ (1 + 2 * (d - 1 - 2 * P.natDegree)) * numerator4 P ^ 2 := by
      congr 2
      omega
    _ = _ := by
      rw [pow_add, pow_one, mul_assoc]
      rw [Nat.mul_comm 2 _, pow_mul]

theorem quadratic4_isHomogeneous : (quadratic4 (K := K)).IsHomogeneous 2 :=
  ((isHomogeneous_X (R := K) (Fin.last 3)).mul (isHomogeneous_X (R := K) (1 : Fin 4))).add
    (isHomogeneous_X_pow 0 2)

theorem numerator4_isHomogeneous (P : Polynomial K) :
    (numerator4 P).IsHomogeneous (2 * P.natDegree) := by
  unfold numerator4 homogeneousParameterPolynomialValue
  apply (Polynomial.isHomogeneous_homogenize P).aeval
  intro i
  fin_cases i
  · exact quadratic4_isHomogeneous
  · exact isHomogeneous_X_pow (Fin.last 3) 2

theorem q4_isHomogeneous (P : Polynomial K) {d : ℕ}
    (hm : 0 < P.natDegree) (hd : 4 * P.natDegree ≤ d) : (q4 P d).IsHomogeneous (d - 1) := by
  unfold q4
  convert (isHomogeneous_X_pow (Fin.last 3) (d - 1 - 2 * P.natDegree)).mul
    (numerator4_isHomogeneous P) using 1
  omega

theorem correction4_isHomogeneous (P : Polynomial K) {d : ℕ}
    (hd : 4 * P.natDegree ≤ d) : (correction4 P d).IsHomogeneous d := by
  unfold correction4
  convert (isHomogeneous_X_pow (Fin.last 3) (d - 4 * P.natDegree)).mul
    ((numerator4_isHomogeneous P).pow 2) using 1
  omega

/-- The canonical ternary perturbation in the affine chart. -/
noncomputable def perturbation3 (P : Polynomial K) : Fin 3 → R₃ :=
  let e := Polynomial.aeval (X 1 + X 0 ^ 2 : R₃) P
  ![e, X 2 - 2 * X 0 * e, e ^ 2]

/-- Polynomial perturbation giving (6.12) in four variables. -/
noncomputable def perturbation4 (P : Polynomial K) (d : ℕ) : Fin 4 → R₄ :=
  ![t * q4 P d, t ^ (d - 1) * X 2 - 2 * X 0 * q4 P d, correction4 P d, 0]

theorem perturbation4_isHomogMap (P : Polynomial K) {d : ℕ}
    (hm : 0 < P.natDegree) (hd : 4 * P.natDegree ≤ d) : IsHomogMap (perturbation4 P d) d := by
  have hq := q4_isHomogeneous P hm hd
  have he : 1 + (d - 1) = d := by omega
  have he' : (d - 1) + 1 = d := by omega
  have hx := (isHomogeneous_X (R := K) (Fin.last 3)).mul hq
  have hy₁ : ((t : R₄) ^ (d - 1) * X 2).IsHomogeneous d := by
    simpa only [he'] using ((isHomogeneous_X_pow (R := K) (Fin.last 3) (d - 1)).mul
      (isHomogeneous_X (R := K) (2 : Fin 4)))
  have hy₂ : (2 * (X 0 : R₄) * q4 P d).IsHomogeneous d := by
    simpa only [map_ofNat, mul_assoc, he] using (((isHomogeneous_X (R := K) (0 : Fin 4)).mul hq).C_mul 2)
  intro j
  fin_cases j
  · change ((t : R₄) * q4 P d).IsHomogeneous d
    simpa only [he] using hx
  · exact hy₁.sub hy₂
  · exact correction4_isHomogeneous P hd
  · exact isHomogeneous_zero (Fin 4) K d

end DimensionFourDependence.TernaryNormalForm
