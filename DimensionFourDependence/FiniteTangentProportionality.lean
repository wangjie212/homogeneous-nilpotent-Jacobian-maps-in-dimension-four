import DimensionFourDependence.OriginalInvariantTangentConstraint

/-! # The quadratic coefficient forces proportionality in an actual finite field

When the quadratic coefficient is kappa/r with kappa in the direction
field, algebraicity of T kappa/r makes r/T algebraic as well. Adjoining
that actual ratio constructs the finite field and its nonzero scalar
expressing r as a multiple of T.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The actual reciprocal tangent ratio is algebraic when the
quadratic coefficient is the specified nonzero coefficient divided by r. -/
theorem quadratic_tangent_constraint_reciprocal_isAlgebraic
    (T r C : E) (hT : T ≠ 0) (hr : r ≠ 0) (κ : F) (hκ : κ ≠ 0)
    (hC : C = algebraMap F E κ / r) (halg : IsAlgebraic F (T * C)) :
    IsAlgebraic F (r / T) := by
  have hκE : algebraMap F E κ ≠ 0 := by
    simpa only [map_zero] using (algebraMap F E).injective.ne hκ
  have he : r / T = algebraMap F E κ * (T * C)⁻¹ := by
    rw [hC]
    field_simp
  rw [he]
  exact (isAlgebraic_algebraMap κ).mul halg.inv

/-- Adjoining the actual nonzero ratio constructs a finite field
containing the actual nonzero proportionality scalar. -/
theorem algebraic_tangent_ratio_constructs_finite_proportionality
    (T r : E) (hT : T ≠ 0) (hr : r ≠ 0) (halg : IsAlgebraic F (r / T)) :
    Module.Finite F (IntermediateField.adjoin F {r / T}) ∧
      ∃ u : IntermediateField.adjoin F {r / T}, u ≠ 0 ∧ r = (u : E) * T := by
  have hfinite : Module.Finite F (IntermediateField.adjoin F {r / T}) :=
    IntermediateField.adjoin.finiteDimensional halg.isIntegral
  let u : IntermediateField.adjoin F {r / T} :=
    ⟨r / T, IntermediateField.subset_adjoin F _ rfl⟩
  refine ⟨hfinite, u, ?_, ?_⟩
  · intro hz
    have he := congrArg (fun z : IntermediateField.adjoin F {r / T} => (z : E)) hz
    exact div_ne_zero hr hT he
  · exact (div_mul_cancel₀ r hT).symm

variable {K : Type*} [Field K] [Algebra K F] [Algebra K E] [IsScalarTower K F E] {n : ℕ}

/-- The original invariant and specified quadratic coefficient
construct the actual finite proportionality extension, without a
supplied algebraicity or annihilating-polynomial hypothesis. -/
theorem original_invariant_constructs_finite_tangent_proportionality
    (A : Fin n → F) (Φ : MvPolynomial (Fin n) K) {δ : ℕ}
    (hΦ : Φ.IsHomogeneous δ) (hirr : Irreducible Φ)
    (hI : (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ})
    (P : MvPolynomial (Option (Fin n)) K) {e : ℕ}
    (hP0 : P ≠ 0) (hP : P.IsHomogeneous e) (hvertex : 0 < P.degreeOf none)
    (x : Fin n → E)
    (hT : (∑ i, aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) * x i) ≠ 0)
    (w : Polynomial E) (hw : w.natDegree ≤ 2)
    (a : E) (hconstant : aeval (fun j : Option (Fin n) => j.elim w
      (fun i => Polynomial.C (x i) + Polynomial.C (algebraMap F E (A i)) * Polynomial.X)) P = Polynomial.C a)
    (r : E) (hr : r ≠ 0) (κ : F) (hκ : κ ≠ 0)
    (hC : w.coeff 2 = algebraMap F E κ / r) :
    let T := ∑ i, aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) * x i
    IsAlgebraic F (r / T) ∧ Module.Finite F (IntermediateField.adjoin F {r / T}) ∧
      ∃ u : IntermediateField.adjoin F {r / T}, u ≠ 0 ∧ r = (u : E) * T := by
  dsimp only
  have halg := original_invariant_tangent_quadratic_isAlgebraic A Φ hΦ hirr hI P hP0 hP hvertex
    x hT w hw a hconstant
  have hratio := quadratic_tangent_constraint_reciprocal_isAlgebraic _ r (w.coeff 2) hT hr κ hκ hC halg
  exact ⟨hratio, algebraic_tangent_ratio_constructs_finite_proportionality _ r hT hr hratio⟩

end DimensionFourDependence
