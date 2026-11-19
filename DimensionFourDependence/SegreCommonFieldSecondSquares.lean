import DimensionFourDependence.SegreNormalizedSecondSquare
import DimensionFourDependence.ClosedParameterVectorDescent

/-! # Both actual ruling squares descend to the common geometric constants -/

namespace DimensionFourDependence

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 2500000

variable {K E : Type u} [Field K] [Field E] [Algebra K E]

/-- The original normalized radial second invariant retains its scalar
and linear square over the common geometric constants, algebraic over
the indicated original ratio alone. -/
def SegreAlgebraicNormalizedSecondSquareFactorization
    (K : Type u) [Field K] [Algebra K E] (Y : Fin 4 → E) (f : E) (d : ℕ) (j : Fin 3) : Prop :=
  ∃ (α : E) (B : Fin 2 → E), α ≠ 0 ∧
    IsAlgebraic (IntermediateField.adjoin K ({Y j.castSucc / Y 0} : Set E)) α ∧
    (∀ i, IsAlgebraic (IntermediateField.adjoin K ({Y j.castSucc / Y 0} : Set E)) (B i)) ∧
    f ^ d / Y 0 ^ 2 = (Polynomial.C α * segreRulingAffineFactor B ^ 2).eval
      (Y (segreRulingRemainingIndex j).castSucc / Y 0)

/-- A finite square value descends with its actual scalar and both
affine coefficients, preserving their smaller parameter algebraicity. -/
theorem finite_parameter_scalar_linear_square_value_descends_to_closed_constants
    [IsAlgClosed E] {κ : Type u} [Field κ] [Algebra E κ] [Algebra K κ] [IsScalarTower K E κ]
    (t s v : E)
    (C : IntermediateField (IntermediateField.adjoin K ({algebraMap E κ t} : Set κ)) κ)
    (hC : Module.Finite (IntermediateField.adjoin K ({algebraMap E κ t} : Set κ)) C)
    (α : C) (hα : α ≠ 0) (b : Fin 2 → C)
    (hvalue : algebraMap E κ v = Polynomial.aeval (algebraMap E κ s)
      (Polynomial.C α * segreRulingAffineFactor b ^ 2)) :
    ∃ (β : E) (B : Fin 2 → E), β ≠ 0 ∧
      IsAlgebraic (IntermediateField.adjoin K ({t} : Set E)) β ∧
      (∀ i, IsAlgebraic (IntermediateField.adjoin K ({t} : Set E)) (B i)) ∧
      v = (Polynomial.C β * segreRulingAffineFactor B ^ 2).eval s := by
  obtain ⟨A, hA, hAalg⟩ := finite_parameter_vector_descends_to_closed_constants t C hC
    (fun _ : Fin 1 => α)
  obtain ⟨B, hB, hBalg⟩ := finite_parameter_vector_descends_to_closed_constants t C hC b
  have hβ : A 0 ≠ 0 := by
    intro hz
    have he := hA 0
    rw [hz, map_zero] at he
    exact ((map_ne_zero (algebraMap C κ)).mpr hα) he.symm
  refine ⟨A 0, B, hβ, hAalg 0, hBalg, ?_⟩
  apply (algebraMap E κ).injective
  rw [hvalue]
  simp only [segreRulingAffineFactor, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, map_mul, map_pow,
    map_add, Polynomial.aeval_C, Polynomial.aeval_X, hA, hB]

/-- Each actual finite boundary square constructs the same kind of
scalar-linear-square identity in the common closed coefficient field. -/
theorem finite_segre_second_square_factors_descend_to_common_geometric_constants
    [IsAlgClosed E] (Y : Fin 4 → E) (f : E) (d : ℕ) (j : Fin 3)
    (hj : j ≠ 0) (hY0 : Y 0 ≠ 0)
    (p : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Option (Fin 4)) E))
    (hfactor : SegreFiniteRadialSecondSquareFactorization K Y f d j p) :
    SegreAlgebraicNormalizedSecondSquareFactorization K Y f d j := by
  obtain ⟨a, _ha, C, hC, P, _hP, _hdegree, hvalue, α, B, hα, hPfactor⟩ :=
    finite_segre_second_square_constructs_normalized_polynomial Y f d j hj hY0 p hfactor
  rw [hPfactor] at hvalue
  exact finite_parameter_scalar_linear_square_value_descends_to_closed_constants
    (Y j.castSucc / Y 0) (Y (segreRulingRemainingIndex j).castSucc / Y 0)
    (f ^ d / Y 0 ^ 2) C hC α hα B hvalue

end DimensionFourDependence
