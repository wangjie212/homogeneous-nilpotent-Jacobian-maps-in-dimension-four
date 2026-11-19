import DimensionFourDependence.ProjectiveNormalizedSection
import DimensionFourDependence.ProjectiveAffineRatioCoordinates

/-! # Normalized original-frame sections retain their coefficients under field identification -/

namespace DimensionFourDependence

variable {k L M : Type*} [Field k] [Field L] [Field M] [Algebra k L] [Algebra k M]

/-- A field identification preserves the three original affine
ratios in their original projective frame order. -/
theorem projectiveAffineRatioCoordinates_field_map (x : Fin 4 → L)
    (f : L →+* M) (s : Fin 4 ≃ Option (Fin 3)) :
    projectiveAffineRatioCoordinates (f ∘ x) s = f ∘ projectiveAffineRatioCoordinates x s := by
  funext i
  exact (map_div₀ f (x (s.symm (some i))) (x (s.symm none))).symm

/-- An identification of the original coefficient fields carries
each entire original projective chart onto its identified ratio chart. -/
theorem projectiveCoordinateChartAlgebra_map_field (x : Fin 4 → L) (e : L ≃ₐ[k] M) (a : Fin 4) :
    (projectiveCoordinateChartAlgebra (C := k) x a).map e.toAlgHom =
      projectiveCoordinateChartAlgebra (C := k) (e ∘ x) a := by
  change (Algebra.adjoin k (Set.range (fun i => x i / x a))).map e.toAlgHom = _
  rw [AlgHom.map_adjoin, ← Set.range_comp]
  have hcoords : e.toAlgHom ∘ (fun i => x i / x a) =
      (fun i => e (x i) / e (x a)) := funext (fun i => map_div₀ e (x i) (x a))
  rw [hcoords]
  rfl

/-- The field identification restricts to the entire original
coordinate-chart algebra. -/
noncomputable def projectiveCoordinateChartFieldMapEquiv (x : Fin 4 → L)
    (e : L ≃ₐ[k] M) (a : Fin 4) :
    projectiveCoordinateChartAlgebra (C := k) x a ≃ₐ[k]
      projectiveCoordinateChartAlgebra (C := k) (e ∘ x) a :=
  (e.subalgebraMap _).trans (Subalgebra.equivOfEq _ _ (projectiveCoordinateChartAlgebra_map_field x e a))

/-- Regular normalized coefficients remain integral over the entire
identified original coordinate chart. -/
theorem projective_normalized_coefficient_isIntegral_field_map
    (x : Fin 4 → L) (e : L ≃ₐ[k] M) (a : Fin 4) {c : L}
    (hc : IsIntegral (projectiveCoordinateChartAlgebra (C := k) x a) c) :
    IsIntegral (projectiveCoordinateChartAlgebra (C := k) (e ∘ x) a) (e c) := by
  apply IsIntegral.map_of_comp_eq (projectiveCoordinateChartFieldMapEquiv x e a).toRingHom
    e.toRingHom _ hc
  apply RingHom.ext
  intro r
  rfl

/-- A normalized original-frame section transported through an
actual coefficient-field identification, retaining every coefficient. -/
noncomputable def projectiveNormalizedSectionFieldMap (x : Fin 4 → L)
    (e : L ≃ₐ[k] M) (s : ProjectiveNormalizedSection (k := k) x) :
    ProjectiveNormalizedSection (k := k) (e ∘ x) where
  coefficient a := ⟨e (s.coefficient a),
    projective_normalized_coefficient_isIntegral_field_map x e a (s.coefficient a).property⟩
  transition i j := by
    simpa only [Function.comp_apply, map_mul] using congrArg e (s.transition i j)

/-- The field transport retains each original rational coefficient
exactly, rather than choosing an unrelated integral representative. -/
theorem projectiveNormalizedSectionFieldMap_coefficient (x : Fin 4 → L)
    (e : L ≃ₐ[k] M) (s : ProjectiveNormalizedSection (k := k) x) (a : Fin 4) :
    ((projectiveNormalizedSectionFieldMap x e s).coefficient a : M) = e (s.coefficient a) := rfl

end DimensionFourDependence
