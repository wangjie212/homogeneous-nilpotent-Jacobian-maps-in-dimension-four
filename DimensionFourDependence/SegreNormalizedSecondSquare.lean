import DimensionFourDependence.SegreZeroPairingFiniteSquare
import DimensionFourDependence.SegreRulingBinaryPolynomial
import DimensionFourDependence.ClosedParameterPolynomialDescent

/-! # The zero-pairing square identities give quadratic ruling polynomials -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [Field E] [Algebra K E]

/-- The radial second invariant, with its radial scale removed, is a
quadratic polynomial in the varying ratio. Its coefficients are algebraic
over the other original ratio alone. -/
def SegreAlgebraicNormalizedSecondSquarePolynomial
    (K : Type u) [Field K] [Algebra K E] (Y : Fin 4 → E) (f : E) (d : ℕ) (j : Fin 3) : Prop :=
  ∃ P : Polynomial E, P ≠ 0 ∧ P.natDegree ≤ 2 ∧
    f ^ d / (Y 0) ^ 2 = P.eval (Y (segreRulingRemainingIndex j).castSucc / Y 0) ∧
    ∀ i, IsAlgebraic (IntermediateField.adjoin K ({Y j.castSucc / Y 0} : Set E)) (P.coeff i)

/-- A square of an original ternary ruling form, divided by the radial
square, gives the corresponding affine linear square exactly. -/
theorem segre_ruling_linear_square_normalized_value
    {C F : Type*} [Field C] [Field F] [Algebra C F]
    (j : Fin 3) (hj : j ≠ 0) (t α : C) (S : Fin 3 → C) (Z : Fin 3 → F)
    (hZ0 : Z 0 ≠ 0) (hrel : Z j = algebraMap C F t * Z 0) :
    algebraMap C F α * ((fun i => algebraMap C F (S i)) ⬝ᵥ Z) ^ 2 / Z 0 ^ 2 =
      Polynomial.aeval (Z (segreRulingRemainingIndex j) / Z 0)
        (Polynomial.C α * segreRulingAffineFactor (segreRulingBinaryCoefficients j t S) ^ 2) := by
  rw [segre_ruling_covector_binary_pairing j hj t S Z hrel]
  simp only [map_mul, map_pow, Polynomial.aeval_C, segreRulingAffineFactor,
    map_add, Polynomial.aeval_X]
  field_simp [hZ0]

/-- An actual finite ruling square factorization constructs a bounded
polynomial in the same normalized point field. -/
theorem finite_segre_second_square_constructs_normalized_polynomial
    (Y : Fin 4 → E) (f : E) (d : ℕ) (j : Fin 3) (hj : j ≠ 0) (hY0 : Y 0 ≠ 0)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hfactor : SegreFiniteRadialSecondSquareFactorization K Y f d j p) :
    ∃ a : Fin 4, X (some a) ∉ p.asHomogeneousIdeal ∧
      ∃ C : IntermediateField (segreProjectiveRulingParameterField K Y j p a)
          (projectivePrimeRatioField p (some a)),
        Module.Finite (segreProjectiveRulingParameterField K Y j p a) C ∧
        ∃ P : Polynomial C, P ≠ 0 ∧ P.natDegree ≤ 2 ∧
          algebraMap E (projectivePrimeRatioField p (some a)) (f ^ d / Y 0 ^ 2) =
            Polynomial.aeval (algebraMap E _ (Y (segreRulingRemainingIndex j).castSucc / Y 0)) P ∧
          ∃ (α : C) (B : Fin 2 → C), α ≠ 0 ∧ P = Polynomial.C α * segreRulingAffineFactor B ^ 2 := by
  obtain ⟨a, ha, C, hC, α, S, hα, _hS, hpower, _hSb, hSY⟩ := hfactor
  let κ := projectivePrimeRatioField p (some a)
  let J := segreProjectiveRulingParameterField K Y j p a
  let tJ : J := ⟨algebraMap E κ (Y j.castSucc / Y 0),
    IntermediateField.subset_adjoin K _ (by rfl)⟩
  let t : C := algebraMap J C tJ
  have ht : algebraMap C κ t = algebraMap E κ (Y j.castSucc / Y 0) := rfl
  let Z : Fin 3 → κ := fun i => algebraMap E κ (Y i.castSucc)
  have hZ0 : Z 0 ≠ 0 := (map_ne_zero (algebraMap E κ)).mpr hY0
  have hrel : Z j = algebraMap C κ t * Z 0 := by
    rw [ht]
    change algebraMap E κ (Y j.castSucc) = algebraMap E κ (Y j.castSucc / Y 0) * algebraMap E κ (Y 0)
    rw [map_div₀]
    exact (div_mul_cancel₀ _ hZ0).symm
  let B := segreRulingAffineFactor (segreRulingBinaryCoefficients j t S)
  let P := Polynomial.C α * B ^ 2
  have hvalue : algebraMap E κ (f ^ d / Y 0 ^ 2) =
      Polynomial.aeval (algebraMap E κ (Y (segreRulingRemainingIndex j).castSucc / Y 0)) P := by
    simp only [map_div₀, map_pow]
    rw [hpower]
    exact segre_ruling_linear_square_normalized_value j hj t α S Z hZ0 hrel
  have hP : P ≠ 0 := by
    intro hz
    have hv : (algebraMap E κ f) ^ d / Z 0 ^ 2 ≠ 0 := by
      rw [hpower]
      exact div_ne_zero (mul_ne_zero ((map_ne_zero (algebraMap C κ)).mpr hα)
        (pow_ne_zero 2 hSY)) (pow_ne_zero 2 hZ0)
    apply hv
    have he := hvalue
    simp only [map_div₀, map_pow, hz, map_zero] at he
    exact he
  refine ⟨a, ha, C, hC, P, hP, ?_, hvalue, α, segreRulingBinaryCoefficients j t S, hα, rfl⟩
  exact Polynomial.natDegree_mul_le.trans (by
    have hB : B.natDegree ≤ 1 := segreRulingAffineFactor_natDegree_le_one _
    have hB2 := Polynomial.natDegree_pow_le (p := B) (n := 2)
    simpa only [Polynomial.natDegree_C, Nat.zero_add] using
      hB2.trans (Nat.mul_le_mul_left 2 hB))

/-- The finite ruling polynomial descends to the common algebraically
closed geometric coefficient field, retaining its quadratic degree bound. -/
theorem finite_segre_second_square_descends_to_geometric_constants
    [IsAlgClosed E] (Y : Fin 4 → E) (f : E) (d : ℕ) (j : Fin 3)
    (hj : j ≠ 0) (hY0 : Y 0 ≠ 0)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hfactor : SegreFiniteRadialSecondSquareFactorization K Y f d j p) :
    SegreAlgebraicNormalizedSecondSquarePolynomial K Y f d j := by
  obtain ⟨a, _ha, C, hC, P, hP, hdegree, hvalue, _hfactor⟩ :=
    finite_segre_second_square_constructs_normalized_polynomial Y f d j hj hY0 p hfactor
  exact finite_parameter_polynomial_descends_to_closed_constants
    (Y j.castSucc / Y 0) (Y (segreRulingRemainingIndex j).castSucc / Y 0)
    (f ^ d / Y 0 ^ 2) C hC P hP hdegree hvalue

end DimensionFourDependence
