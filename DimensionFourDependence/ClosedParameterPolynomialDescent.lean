import DimensionFourDependence.AlgebraicParameterReflection
import DimensionFourDependence.AlgebraicPolynomialDescent

/-! # Finite parameter polynomials descend to the original closed geometric constants -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K E κ : Type u} [Field K] [Field E] [IsAlgClosed E] [Field κ]
    [Algebra K E] [Algebra E κ] [Algebra K κ] [IsScalarTower K E κ]

/-- A polynomial over an actual finite extension of the mapped parameter
field has an original closed-constant-field polynomial with the same value,
degree bound and smaller original parameter algebraicity of every coefficient. -/
theorem finite_parameter_polynomial_descends_to_closed_constants
    (t z v : E)
    (C : IntermediateField (IntermediateField.adjoin K ({algebraMap E κ t} : Set κ)) κ)
    (hC : Module.Finite (IntermediateField.adjoin K ({algebraMap E κ t} : Set κ)) C)
    (P : Polynomial C) (hP : P ≠ 0) {N : ℕ} (hdegree : P.natDegree ≤ N)
    (hvalue : algebraMap E κ v = Polynomial.aeval (algebraMap E κ z) P) :
    ∃ Q : Polynomial E, Q ≠ 0 ∧ Q.natDegree ≤ N ∧ v = Q.eval z ∧
      ∀ i, IsAlgebraic (IntermediateField.adjoin K ({t} : Set E)) (Q.coeff i) := by
  let J := IntermediateField.adjoin K ({algebraMap E κ t} : Set κ)
  let : Module.Finite J C := hC
  let Pκ := P.map (algebraMap C κ)
  have hcoeff (i : ℕ) : IsAlgebraic J (Pκ.coeff i) := by
    rw [Polynomial.coeff_map]
    exact (IsAlgebraic.of_finite (R := J) (P.coeff i)).algHom (IsScalarTower.toAlgHom J C κ)
  have hJ : J ≤ (IsScalarTower.toAlgHom K E κ).fieldRange := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨t, rfl⟩
  have hcoeffE (i : ℕ) : IsAlgebraic E (Pκ.coeff i) :=
    isAlgebraic_of_subfield_le_coefficient_image J hJ _ (hcoeff i)
  obtain ⟨Q, hQ⟩ := integral_polynomial_coefficients_construct_base_polynomial Pκ
    (fun i => (hcoeffE i).isIntegral)
  have hQ0 : Q ≠ 0 := by
    intro hz
    have hPκ : Pκ ≠ 0 := Polynomial.map_ne_zero hP
    apply hPκ
    rw [← hQ, hz, Polynomial.map_zero]
  have hdegreeQ : Q.natDegree = P.natDegree := by
    calc
      _ = (Q.map (algebraMap E κ)).natDegree := (Polynomial.natDegree_map _).symm
      _ = Pκ.natDegree := congrArg Polynomial.natDegree hQ
      _ = P.natDegree := Polynomial.natDegree_map _
  have hvalueQ : algebraMap E κ (Q.eval z) = Polynomial.aeval (algebraMap E κ z) P := by
    calc
      _ = (Q.map (algebraMap E κ)).eval (algebraMap E κ z) := by
        rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
      _ = Pκ.eval (algebraMap E κ z) := congrArg (fun A : Polynomial κ => A.eval (algebraMap E κ z)) hQ
      _ = _ := by rw [Polynomial.eval_map]; rfl
  refine ⟨Q, hQ0, hdegreeQ.le.trans hdegree,
    (algebraMap E κ).injective (hvalue.trans hvalueQ.symm), ?_⟩
  intro i
  apply algebraic_over_mapped_parameter_reflects (IsScalarTower.toAlgHom K E κ) t (Q.coeff i)
  change IsAlgebraic J (algebraMap E κ (Q.coeff i))
  have hi : algebraMap E κ (Q.coeff i) = Pκ.coeff i := by
    rw [← Polynomial.coeff_map, hQ]
  rw [hi]
  exact hcoeff i

end DimensionFourDependence
