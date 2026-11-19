import DimensionFourDependence.ClosedParameterPolynomialDescent
import DimensionFourDependence.SegreRulingBinaryPolynomial

/-! # The actual finite ruling covectors descend to the same closed geometric constants -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 2000000

variable {K E κ : Type u} [Field K] [Field E] [IsAlgClosed E] [Field κ]
    [Algebra K E] [Algebra E κ] [Algebra K κ] [IsScalarTower K E κ]

/-- Every coordinate of an actual finite parameter vector has a
specified original geometric-constant preimage, algebraic over the
original parameter alone. The entire original image is retained. -/
theorem finite_parameter_vector_descends_to_closed_constants
    (t : E)
    (C : IntermediateField (IntermediateField.adjoin K ({algebraMap E κ t} : Set κ)) κ)
    (hC : Module.Finite (IntermediateField.adjoin K ({algebraMap E κ t} : Set κ)) C)
    {n : ℕ} (a : Fin n → C) :
    ∃ A : Fin n → E, (∀ i, algebraMap E κ (A i) = algebraMap C κ (a i)) ∧
      ∀ i, IsAlgebraic (IntermediateField.adjoin K ({t} : Set E)) (A i) := by
  let J := IntermediateField.adjoin K ({algebraMap E κ t} : Set κ)
  let : Module.Finite J C := hC
  have hJ : J ≤ (IsScalarTower.toAlgHom K E κ).fieldRange := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨t, rfl⟩
  have halg (i : Fin n) : IsAlgebraic J (algebraMap C κ (a i)) :=
    (IsAlgebraic.of_finite (R := J) (a i)).algHom (IsScalarTower.toAlgHom J C κ)
  have hex (i : Fin n) : ∃ x : E, algebraMap E κ x = algebraMap C κ (a i) :=
    algebraic_value_preimage_of_isAlgClosed _
      (isAlgebraic_of_subfield_le_coefficient_image J hJ _ (halg i))
  choose A hA using hex
  refine ⟨A, hA, ?_⟩
  intro i
  apply algebraic_over_mapped_parameter_reflects (IsScalarTower.toAlgHom K E κ) t (A i)
  change IsAlgebraic J (algebraMap E κ (A i))
  rw [hA i]
  exact halg i

/-- The complete actual linear-times-power ruling presentation descends
to the closed geometric constants while retaining both original
parameter-algebraic coefficient vectors and their exact original images. -/
theorem finite_parameter_linear_power_value_descends_to_closed_constants
    (t s v : E)
    (C : IntermediateField (IntermediateField.adjoin K ({algebraMap E κ t} : Set κ)) κ)
    (hC : Module.Finite (IntermediateField.adjoin K ({algebraMap E κ t} : Set κ)) C)
    (a b : Fin 2 → C) (d : ℕ)
    (hvalue : algebraMap E κ v =
      Polynomial.aeval (algebraMap E κ s) (segreRulingPowerPolynomial a b d)) :
    ∃ A B : Fin 2 → E,
      (∀ i, algebraMap E κ (A i) = algebraMap C κ (a i)) ∧
      (∀ i, algebraMap E κ (B i) = algebraMap C κ (b i)) ∧
      (∀ i, IsAlgebraic (IntermediateField.adjoin K ({t} : Set E)) (A i)) ∧
      (∀ i, IsAlgebraic (IntermediateField.adjoin K ({t} : Set E)) (B i)) ∧
      v = (segreRulingPowerPolynomial A B d).eval s := by
  obtain ⟨A, hA, hAalg⟩ := finite_parameter_vector_descends_to_closed_constants t C hC a
  obtain ⟨B, hB, hBalg⟩ := finite_parameter_vector_descends_to_closed_constants t C hC b
  refine ⟨A, B, hA, hB, hAalg, hBalg, ?_⟩
  apply (algebraMap E κ).injective
  rw [hvalue]
  simp only [segreRulingPowerPolynomial, segreRulingAffineFactor, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
    map_mul, map_pow, map_add, Polynomial.aeval_C, Polynomial.aeval_X, hA, hB]

end DimensionFourDependence
