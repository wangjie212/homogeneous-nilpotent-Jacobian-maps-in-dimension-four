import DimensionFourDependence.CompatibleGeometricParameterFrame

/-! # Parameter coefficient algebraicity reflects through the actual source realization -/

namespace DimensionFourDependence

variable {K E F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F]

/-- A specified field embedding both preserves and reflects
algebraicity over the exact image of the same rational parameter. -/
theorem parameter_algebraic_coefficient_map_iff
    (p : RatFunc K →ₐ[K] E) (f : E →ₐ[K] F) (a : E) :
    IsAlgebraic (f.comp p).fieldRange (f a) ↔ IsAlgebraic p.fieldRange a := by
  let e := p.equivFieldRange.symm.trans (f.comp p).equivFieldRange
  have hcoeff (c : p.fieldRange) : (e c : F) = f (c : E) := by
    obtain ⟨r, rfl⟩ := p.equivFieldRange.surjective c
    simp only [e, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
    rfl
  apply isAlgebraic_ringHom_iff_of_comp_eq e.toRingEquiv f.toRingHom f.injective
  apply RingHom.ext
  intro c
  exact hcoeff c

variable [CharZero K] [Algebra E F] [IsScalarTower K E F]
    [Algebra (FractionRing (MvPolynomial (Fin 4) K)) F]
    [IsScalarTower K (FractionRing (MvPolynomial (Fin 4) K)) F]
    [Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin 4) K)) F]

/-- A constructed numerator in the actual geometric constants is
algebraic over the realized closed Gauss field exactly when its source
image is algebraic over the source parameter field. -/
theorem compatible_closed_parameter_coefficient_image_isAlgebraic_iff
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (g : closedGaussParameterField H I →ₐ[K] E)
    (hg : ∀ c : closedGaussParameterField H I, algebraMap E F (g c) =
      algebraMap (FractionRing (MvPolynomial (Fin 4) K)) F
        (c : FractionRing (MvPolynomial (Fin 4) K))) (a : E) :
    IsAlgebraic ((IsScalarTower.toAlgHom K (FractionRing (MvPolynomial (Fin 4) K)) F).comp
      (closedGaussParameterSourceHom H I e)).fieldRange (algebraMap E F a) ↔ IsAlgebraic g.fieldRange a := by
  rw [compatible_closed_parameter_source_realization H I e g hg]
  rw [← algHom_parameter_equiv_fieldRange e g]
  exact parameter_algebraic_coefficient_map_iff (g.comp e.toAlgHom) (IsScalarTower.toAlgHom K E F) a

end DimensionFourDependence
