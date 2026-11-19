import DimensionFourDependence.LinearPolynomialCoordinates
import DimensionFourDependence.PrimitiveMapDegree

/-! # Actual polynomial source and target conjugacy

Two inverse constant matrices construct inverse substitutions on the
original polynomial ring and its fraction field. Applying the inverse
matrix on the output preserves homogeneity and nilpotence. The chain
rule gives the full Jacobian similarity identity.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] {n : ℕ}

/-- Inverse matrices give the exact inverse polynomial substitution. -/
theorem matrix_linear_polynomial_substitution_inverse
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1)
    (p : MvPolynomial (Fin n) K) :
    linearPolynomialPullback S (linearPolynomialPullback T p) = p := by
  have ht : S.transpose * T.transpose = 1 := by
    rw [← Matrix.transpose_mul, hTS, Matrix.transpose_one]
  change aeval (fun i => ∑ k, C (S i k) * X k)
    (aeval (fun j => ∑ i, C (T j i) * X i) p) = p
  simpa only [Matrix.transpose_apply] using
    aeval_aeval_linear_of_mul_eq_one T.transpose S.transpose ht p

/-- The actual original polynomial-ring automorphism constructed from
an inverse pair of constant coordinate matrices. -/
noncomputable def matrixPolynomialCoordinateEquiv
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1) :
    MvPolynomial (Fin n) K ≃ₐ[K] MvPolynomial (Fin n) K :=
  AlgEquiv.ofAlgHom (aeval (linearPolynomialMap T)) (aeval (linearPolynomialMap S))
    (by
      apply AlgHom.ext
      intro p
      exact matrix_linear_polynomial_substitution_inverse S T hST p)
    (by
      apply AlgHom.ext
      intro p
      exact matrix_linear_polynomial_substitution_inverse T S hTS p)

/-- Its forward map is precisely the original matrix substitution. -/
theorem matrixPolynomialCoordinateEquiv_apply
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (p : MvPolynomial (Fin n) K) :
    matrixPolynomialCoordinateEquiv T S hTS hST p = linearPolynomialPullback T p := rfl

/-- The source-coordinate change on the actual original source field. -/
noncomputable def matrixSourceFractionEquiv
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1) :
    FractionRing (MvPolynomial (Fin n) K) ≃ₐ[K] FractionRing (MvPolynomial (Fin n) K) :=
  IsFractionRing.algEquivOfAlgEquiv (matrixPolynomialCoordinateEquiv T S hTS hST)

/-- The source-field change agrees with substitution on every original
source polynomial, not just the coordinate generators. -/
theorem matrixSourceFractionEquiv_polynomial
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (p : MvPolynomial (Fin n) K) :
    matrixSourceFractionEquiv T S hTS hST
      (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) p) =
      algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
        (linearPolynomialPullback T p) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap _ p

/-- Conjugation substitutes x=Tz and applies S to the original outputs. -/
noncomputable def linearPolynomialConjugate
    (T S : Matrix (Fin n) (Fin n) K) (H : Fin n → MvPolynomial (Fin n) K) :
    Fin n → MvPolynomial (Fin n) K :=
  fun i => ∑ j, C (S i j) * linearPolynomialPullback T (H j)

/-- The same original homogeneous degree survives source and target
conjugacy. -/
theorem linearPolynomialConjugate_homogeneous
    (T S : Matrix (Fin n) (Fin n) K) (H : Fin n → MvPolynomial (Fin n) K)
    {d : ℕ} (hH : IsHomogMap H d) :
    IsHomogMap (linearPolynomialConjugate T S H) d := by
  intro i
  apply IsHomogeneous.sum
  intro j _
  exact (linearPolynomialPullback_homogeneous T (H j) (hH j)).C_mul (S i j)

/-- The full polynomial Jacobian identity for source and target
conjugacy, with every original Jacobian entry substituted. -/
theorem jac_linearPolynomialConjugate
    (T S : Matrix (Fin n) (Fin n) K) (H : Fin n → MvPolynomial (Fin n) K) :
    jac (linearPolynomialConjugate T S H) =
      S.map MvPolynomial.C * (jac H).map (aeval (linearPolynomialMap T)) * T.map MvPolynomial.C := by
  have hder (i j : Fin n) : pderiv j (linearPolynomialMap T i) = C (T i j) :=
    congrFun (congrFun (jac_linearPolynomialMap T) i) j
  rw [Matrix.mul_assoc]
  ext i j
  simp only [jac, Matrix.of_apply, linearPolynomialConjugate, map_sum,
    Derivation.leibniz, smul_eq_mul, pderiv_C, mul_zero, add_zero,
    linearPolynomialPullback, pderiv_aeval, hder, Matrix.mul_apply,
    Matrix.map_apply, Finset.mul_sum]

/-- An inverse source and output change preserves nilpotence of the
actual polynomial Jacobian. -/
theorem linearPolynomialConjugate_nilpotent
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin n → MvPolynomial (Fin n) K) (hN : IsNilpotent (jac H)) :
    IsNilpotent (jac (linearPolynomialConjugate T S H)) := by
  let Φ := fun i => linearPolynomialPullback T (H i)
  have hrestore : (fun i => aeval (linearPolynomialMap S) (Φ i)) = H := by
    funext i
    exact matrix_linear_polynomial_substitution_inverse T S hTS (H i)
  have ht : T.transpose * S.transpose = 1 := by
    rw [← Matrix.transpose_mul, hST, Matrix.transpose_one]
  have hinj : Function.Injective (aeval (R := K) (linearPolynomialMap S)) :=
    aeval_injective_of_mul_eq_one S.transpose T.transpose ht (linearPolynomialMap S) (fun _ => rfl)
  have hn : IsNilpotent (jac fun i => aeval (linearPolynomialMap S) (Φ i)) := by
    rw [hrestore]
    exact hN
  have he := isNilpotent_jac_of_linear_subst S.transpose (linearPolynomialMap S)
    (fun _ => rfl) hinj Φ hn
  change IsNilpotent (jac fun j => ∑ i, C (S j i) * linearPolynomialPullback T (H i))
  simpa only [Matrix.transpose_apply, Φ] using he

/-- Invertible source and target changes preserve component independence
over the original constant field. -/
theorem linearPolynomialConjugate_componentsIndependent
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin n → MvPolynomial (Fin n) K) (hind : ¬ ComponentsDependent H) :
    ¬ ComponentsDependent (linearPolynomialConjugate T S H) := by
  classical
  rintro ⟨c, hc, hzero⟩
  let b : Fin n → K := fun k => ∑ i, c i * S i k
  have hexpand : ∑ i, c i • linearPolynomialConjugate T S H i =
      linearPolynomialPullback T (∑ k, b k • H k) := by
    simp only [linearPolynomialConjugate, Finset.smul_sum, smul_eq_C_mul,
      linearPolynomialPullback, map_sum, map_mul, aeval_C, algebraMap_eq,
      b, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc]
  have hb : ∑ k, b k • H k = 0 := by
    apply (matrixPolynomialCoordinateEquiv T S hTS hST).injective
    change linearPolynomialPullback T (∑ k, b k • H k) =
      linearPolynomialPullback T 0
    rw [← hexpand, hzero]
    exact (map_zero _).symm
  have hbzero : b = 0 :=
    funext (Fintype.linearIndependent_iff.mp (linearIndependent_of_componentsIndependent H hind) b hb)
  have hbvec : c ᵥ* S = 0 := hbzero
  apply hc
  have he := congrArg (fun v => v ᵥ* T) hbvec
  rw [Matrix.vecMul_vecMul, hST, Matrix.vecMul_one, Matrix.zero_vecMul] at he
  exact he

end DimensionFourDependence
