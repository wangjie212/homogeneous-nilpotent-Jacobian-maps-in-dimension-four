import DimensionFourDependence.PolynomialCovectorCoefficientKernel

/-! # Cofinitely many actual parameter incidences give every original coefficient equation -/

namespace DimensionFourDependence

open Matrix

variable {K E : Type*} [Field K] [Infinite K] [Field E] [Algebra K E] {n : ℕ}

/-- Incidence at all but finitely many original parameter values is
the full polynomial identity, also when the point coordinates belong
to an extension field. -/
theorem cofinite_parameter_incidence_mem_extended_coefficient_kernel
    (v : Fin n → Polynomial K) (x : Fin n → E) (S : Set K) (hS : S.Finite)
    (hinc : ∀ a ∉ S, ∑ i, algebraMap K E ((v i).eval a) * x i = 0) :
    (polynomialCovectorCoefficientMatrix v).map (algebraMap K E) *ᵥ x = 0 := by
  let P : Polynomial E := ∑ i, Polynomial.C (x i) * (v i).map (algebraMap K E)
  have hroot (a : K) (ha : a ∉ S) : P.IsRoot (algebraMap K E a) := by
    change P.eval (algebraMap K E a) = 0
    simpa only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_map_algebraMap, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
      mul_comm] using hinc a ha
  have hinf : (Sᶜ).Infinite := hS.infinite_compl
  have himage : ((algebraMap K E) '' Sᶜ).Infinite := hinf.image (algebraMap K E).injective.injOn
  have hzero : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P (himage.mono (by
    rintro y ⟨a, ha, rfl⟩
    exact hroot a ha))
  exact polynomial_covector_relation_mem_extended_coefficient_kernel v x hzero

end DimensionFourDependence
