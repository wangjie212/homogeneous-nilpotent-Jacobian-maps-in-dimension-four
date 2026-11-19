import DimensionFourDependence.ParameterLinearSourceValue
import DimensionFourDependence.EulerHomogeneousFractions
import DimensionFourDependence.LinearSubst

/-! # A regular parameter-linear source factor is an original linear form

Polynomiality is supplied by the valuative scalar-factor argument.
The original source Euler derivation gives the factor weight one when
the parameter has weight zero. Injectivity into the source field then
makes the constructed source polynomial homogeneous of degree one,
with a covector in the original constant field.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K] [CharZero K] {n m : ℕ}

/-- A polynomial of source Euler weight one is homogeneous of degree one,
including the zero polynomial. -/
theorem sourceEuler_weight_one_polynomial_homogeneous
    (Z : MvPolynomial (Fin n) K)
    (hZ : sourceEuler (K := K) (algebraMap (MvPolynomial (Fin n) K)
      (FractionRing (MvPolynomial (Fin n) K)) Z) =
        algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) Z) :
    Z.IsHomogeneous 1 := by
  by_cases hz : Z = 0
  · rw [hz]
    exact isHomogeneous_zero (Fin n) K 1
  have he : polynomialEuler Z = C (1 : K) * Z := by
    apply IsFractionRing.injective (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
    rw [sourceEuler_polynomial] at hZ
    simpa only [map_mul, map_one, one_mul] using hZ
  obtain ⟨d, hd, hweight⟩ := polynomialEuler_eigenvector_homogeneous Z hz 1 he
  have hdegree : d = 1 := by exact_mod_cast hweight.symm
  simpa only [hdegree] using hd

/-- A polynomial-parameter linear source value with a nonconstant
polynomial scalar product constructs an original source linear form.
Both its exact value and its constant covector are constructed. -/
theorem polynomial_parameter_linear_value_constructs_source_linear_form
    (t : FractionRing (MvPolynomial (Fin n) K)) (ht : sourceEuler (K := K) t = 0)
    (j : Fin m → Fin n) (v : Fin m → Polynomial K)
    (A : Polynomial K) (hA : 0 < A.natDegree) (d : ℕ) (H : MvPolynomial (Fin n) K)
    (hH : algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) H =
      Polynomial.aeval t A *
        (MvPolynomial.eval₂ (Polynomial.aeval t).toRingHom
          (fun i => rationalCoordinate (K := K) (j i)) (polynomialParameterLinearForm v)) ^ d) :
    ∃ Z : MvPolynomial (Fin n) K,
      algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) Z =
        MvPolynomial.eval₂ (Polynomial.aeval t).toRingHom
          (fun i => rationalCoordinate (K := K) (j i)) (polynomialParameterLinearForm v) ∧
      Z.IsHomogeneous 1 ∧ ∃ c : Fin n → K, Z = linearFormPolynomial c := by
  obtain ⟨Z, hZ⟩ := polynomial_parameter_linear_form_source_value_regular
    t v (fun i => X (j i)) A hA d H (by simpa only [rationalCoordinate] using hH)
  have hZvalue : algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) Z =
      MvPolynomial.eval₂ (Polynomial.aeval t).toRingHom
        (fun i => rationalCoordinate (K := K) (j i)) (polynomialParameterLinearForm v) := by
    simpa only [rationalCoordinate] using hZ
  have hweight := polynomial_parameter_linear_form_derivation_weight_one
    (sourceEuler (K := K)) t ht v (fun i => rationalCoordinate (K := K) (j i))
      (fun i => sourceEuler_coordinate (j i))
  have hhom : Z.IsHomogeneous 1 := sourceEuler_weight_one_polynomial_homogeneous Z
    (by rw [hZvalue]; exact hweight)
  refine ⟨Z, hZvalue, hhom, fun i => (pderiv i Z).coeff 0, ?_⟩
  exact eq_sum_of_isHomogeneous_one hhom

end DimensionFourDependence
