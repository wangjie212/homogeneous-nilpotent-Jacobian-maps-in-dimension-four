import DimensionFourDependence.FiniteCoefficientScalarEquiv

/-! # The finite boundary coefficients have the specified original Gauss action

A rational parameter identifies the original closed Gauss field with its
actual image in the boundary field. Finite extensions of that image
therefore acquire a finite original Gauss action, compatible with the
actual boundary embedding.
-/

namespace DimensionFourDependence

variable {K C L κ : Type*} [Field K] [Field C] [Field L] [Field κ]
    [Algebra K C] [Algebra K L] [Algebra K κ]

/-- The original closed parameter field is identified with the
specified actual boundary image through the chosen rational parameter. -/
noncomputable def parameterImageOriginalFieldEquiv
    (a : C →ₐ[K] L) (e : RatFunc K ≃ₐ[K] C) (g : L →ₐ[K] κ) :
    C ≃ₐ[K] (g.comp (a.comp e.toAlgHom)).fieldRange :=
  e.symm.trans (g.comp (a.comp e.toAlgHom)).equivFieldRange

/-- This identification recovers the original boundary realization
on every original closed Gauss coefficient. -/
theorem parameterImageOriginalFieldEquiv_value
    (a : C →ₐ[K] L) (e : RatFunc K ≃ₐ[K] C) (g : L →ₐ[K] κ) (c : C) :
    (parameterImageOriginalFieldEquiv a e g c : κ) = g (a c) := by
  change g (a (e (e.symm c))) = g (a c)
  rw [e.apply_symm_apply]

/-- The original closed Gauss action on the actual finite boundary
coefficient field uses the specified parameter image identification. -/
@[instance_reducible]
noncomputable def parameterImageFiniteExtensionAlgebra
    (a : C →ₐ[K] L) (e : RatFunc K ≃ₐ[K] C) (g : L →ₐ[K] κ)
    (E : IntermediateField (g.comp (a.comp e.toAlgHom)).fieldRange κ) : Algebra C E :=
  finiteCoefficientScalarAlgebra (E := E) (parameterImageOriginalFieldEquiv a e g).toRingEquiv

/-- The specified finite coefficient action retains each actual
rational parameter value through the exact original field-range map. -/
theorem parameterImageFiniteExtensionAlgebra_parameter_value
    (a : C →ₐ[K] L) (e : RatFunc K ≃ₐ[K] C) (g : L →ₐ[K] κ)
    (E : IntermediateField (g.comp (a.comp e.toAlgHom)).fieldRange κ) (r : RatFunc K) :
    letI : Algebra C E := parameterImageFiniteExtensionAlgebra a e g E
    algebraMap C E (e r) = algebraMap (g.comp (a.comp e.toAlgHom)).fieldRange E
      ((g.comp (a.comp e.toAlgHom)).equivFieldRange r) := by
  let : Algebra C E := parameterImageFiniteExtensionAlgebra a e g E
  change algebraMap (g.comp (a.comp e.toAlgHom)).fieldRange E
    ((g.comp (a.comp e.toAlgHom)).equivFieldRange (e.symm (e r))) = _
  rw [e.symm_apply_apply]

/-- The constructed boundary coefficients are finite over the
original closed Gauss field itself. -/
theorem parameterImageFiniteExtensionAlgebra_finite
    (a : C →ₐ[K] L) (e : RatFunc K ≃ₐ[K] C) (g : L →ₐ[K] κ)
    (E : IntermediateField (g.comp (a.comp e.toAlgHom)).fieldRange κ)
    [Module.Finite (g.comp (a.comp e.toAlgHom)).fieldRange E] :
    letI : Algebra C E := parameterImageFiniteExtensionAlgebra a e g E
    Module.Finite C E :=
  finiteCoefficientScalarAlgebra_finite (E := E) (parameterImageOriginalFieldEquiv a e g).toRingEquiv

/-- The constructed action on finite coefficients is compatible
with their actual inclusion in the boundary field. -/
theorem parameterImageFiniteExtensionAlgebra_target_tower
    (a : C →ₐ[K] L) (e : RatFunc K ≃ₐ[K] C) (g : L →ₐ[K] κ)
    (E : IntermediateField (g.comp (a.comp e.toAlgHom)).fieldRange κ) :
    letI : Algebra C κ := (g.comp a).toRingHom.toAlgebra
    letI : Algebra C E := parameterImageFiniteExtensionAlgebra a e g E
    IsScalarTower C E κ := by
  let : Algebra C κ := (g.comp a).toRingHom.toAlgebra
  exact finiteCoefficientScalarAlgebra_target_tower
    (E := E) (parameterImageOriginalFieldEquiv a e g).toRingEquiv
    (fun c => (parameterImageOriginalFieldEquiv_value a e g c).symm)

end DimensionFourDependence
