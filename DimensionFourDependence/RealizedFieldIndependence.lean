import DimensionFourDependence.ClosedGaussTransverseIndependence

/-! # Source independence over the actual realized coefficient field

A compatible source embedding and coefficient-field embedding transport
independence to the coefficient embedding's actual field range. Thus a
larger source field need not be identified with the geometric field.
-/

namespace DimensionFourDependence

variable {K C M E G σ : Type*} [Field K] [Field C] [Field M] [Field E] [Field G]
    [Algebra K C] [Algebra K M] [Algebra C M] [IsScalarTower K C M]
    [Algebra K E] [Algebra K G] [Algebra E G] [IsScalarTower K E G]

/-- Every actual compatible realization preserves independence over
the same original coefficient field's entire actual field range. -/
theorem independent_source_coordinates_over_realized_coefficient_field
    (g : C →ₐ[K] E) [Algebra g.fieldRange G]
    (f : M →ₐ[K] G)
    (hcomp : ∀ c : C, algebraMap g.fieldRange G (g.equivFieldRange c) = f (algebraMap C M c))
    (x : σ → M) (hx : AlgebraicIndependent C x) :
    AlgebraicIndependent g.fieldRange (fun i => f (x i)) := by
  have he : (algebraMap g.fieldRange G).comp g.equivFieldRange.toRingHom =
      f.toRingHom.comp (algebraMap C M) := by
    ext c
    change algebraMap g.fieldRange G (g.equivFieldRange c) = f (algebraMap C M c)
    exact hcomp c
  exact (algebraicIndependent_ringHom_iff_of_comp_eq g.equivFieldRange.toRingEquiv
    f.toRingHom f.injective he).mpr hx

end DimensionFourDependence
