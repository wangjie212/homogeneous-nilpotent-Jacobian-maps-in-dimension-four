import DimensionFourDependence.AlgebraicCoefficientEmbedding
import DimensionFourDependence.ParabolaFieldEmbedding

/-! # Factoring an actual constant-field realization

An embedding whose values are algebraic over algebraically closed
geometric constants factors through those constants. The factor retains
the original constant field and the actual value of every coefficient.
-/

namespace DimensionFourDependence

variable {K C E G : Type*} [Field K] [Field C] [Field E] [Field G]
    [Algebra K C] [Algebra K E] [Algebra K G] [Algebra E G] [IsScalarTower K E G]
    [IsAlgClosed E]

/-- Every algebraic coefficient image has an actual preimage in the
geometric constants; these preimages form one compatible field embedding. -/
theorem algebraic_images_construct_constant_field_factorization
    (f : C →ₐ[K] G) (halg : ∀ c : C, IsAlgebraic E (f c)) :
    ∃ g : C →ₐ[K] E, ∀ c : C, algebraMap E G (g c) = f c := by
  classical
  have hpre (c : C) : ∃ a : E, algebraMap E G a = f c :=
    algebraic_value_preimage_of_isAlgClosed (f c) (halg c)
  let g : C → E := fun c => Classical.choose (hpre c)
  have hg (c : C) : algebraMap E G (g c) = f c := Classical.choose_spec (hpre c)
  refine ⟨{
    toFun := g
    map_zero' := by
      apply (algebraMap E G).injective
      rw [hg, map_zero, map_zero]
    map_one' := by
      apply (algebraMap E G).injective
      rw [hg, map_one, map_one]
    map_add' := by
      intro a b
      apply (algebraMap E G).injective
      simp only [hg, map_add]
    map_mul' := by
      intro a b
      apply (algebraMap E G).injective
      simp only [hg, map_mul]
    commutes' := by
      intro k
      apply (algebraMap E G).injective
      rw [hg, f.commutes, ← IsScalarTower.algebraMap_apply K E G] }, hg⟩

end DimensionFourDependence
