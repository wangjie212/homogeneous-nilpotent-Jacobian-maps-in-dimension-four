import DimensionFourDependence.ProjectiveConeCoordinateAlgebra

/-! # Original projective-coordinate constants lift to the actual cone fraction field -/

namespace DimensionFourDependence

variable {E F : Type*} [Field E] [Field F] [Algebra E F]
  (x : Fin 3 → F) (hgen : IntermediateField.adjoin E (Set.range x) = ⊤)

local notation "A₀" => projectiveConeCoordinateAlgebra (E := E) x
local notation "φ₀" => projectiveConeFractionEmbedding (E := E) x

include hgen

/-- Dividing each original cone coordinate by the original radial
coordinate recovers every generating constant, hence the whole original
point field inside the actual cone fraction embedding. -/
theorem projectiveConeFractionEmbedding_constants_mem_fieldRange (u : F) :
    RatFunc.C u ∈ (φ₀).fieldRange := by
  let γ := IsScalarTower.toAlgHom E F (RatFunc F)
  have hcoord (j : Option (Fin 3)) :
      φ₀ (algebraMap A₀ (FractionRing A₀) (projectiveConeCoordinate (E := E) x j)) ∈ (φ₀).fieldRange :=
    AlgHom.mem_fieldRange.mpr ⟨_, rfl⟩
  have ht : (RatFunc.X : RatFunc F) ∈ (φ₀).fieldRange := by
    simpa only [projectiveConeFractionEmbedding_coordinate, Option.elim_none, map_one, one_mul] using hcoord none
  have hle : IntermediateField.adjoin E (Set.range x) ≤ (φ₀).fieldRange.comap γ := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨j, rfl⟩
    change RatFunc.C (x j) ∈ (φ₀).fieldRange
    have hj : RatFunc.C (x j) * RatFunc.X ∈ (φ₀).fieldRange := by
      simpa only [projectiveConeFractionEmbedding_coordinate, Option.elim_some] using hcoord (some j)
    have hdiv := (φ₀).fieldRange.div_mem hj ht
    have he : (RatFunc.C (x j) * RatFunc.X) / RatFunc.X = RatFunc.C (x j) :=
      mul_div_cancel_right₀ _ RatFunc.X_ne_zero
    exact he ▸ hdiv
  exact hle (by rw [hgen]; trivial)

/-- The original point field maps into the actual cone fraction
field by the inverse of its actual embedded field range. -/
noncomputable def projectiveConeFractionConstantHom : F →ₐ[E] FractionRing A₀ := by
  let c : F →ₐ[E] (φ₀).fieldRange :=
    { toFun := fun u => ⟨RatFunc.C u, projectiveConeFractionEmbedding_constants_mem_fieldRange x hgen u⟩
      map_zero' := Subtype.ext (map_zero RatFunc.C)
      map_one' := Subtype.ext (map_one RatFunc.C)
      map_add' := fun u v => Subtype.ext (map_add RatFunc.C u v)
      map_mul' := fun u v => Subtype.ext (map_mul RatFunc.C u v)
      commutes' := fun e => Subtype.ext ((IsScalarTower.toAlgHom E F (RatFunc F)).commutes e) }
  exact (φ₀).equivFieldRange.symm.toAlgHom.comp c

/-- The lift retains the exact original constant in the same
radial rational-function field. -/
theorem projectiveConeFractionConstantHom_value (u : F) :
    φ₀ (projectiveConeFractionConstantHom x hgen u) = RatFunc.C u := by
  change (((φ₀).equivFieldRange) (((φ₀).equivFieldRange).symm
    ⟨RatFunc.C u, projectiveConeFractionEmbedding_constants_mem_fieldRange x hgen u⟩) : RatFunc F) = _
  rw [AlgEquiv.apply_symm_apply]

/-- Multiplying a lifted original point coordinate by the actual
radial coordinate gives exactly its original homogeneous cone coordinate. -/
theorem projectiveConeFractionConstantHom_mul_radial_coordinate (i : Option (Fin 3)) :
    projectiveConeFractionConstantHom x hgen (i.elim 1 x) *
      algebraMap A₀ (FractionRing A₀) (projectiveConeCoordinate (E := E) x none) =
        algebraMap A₀ (FractionRing A₀) (projectiveConeCoordinate (E := E) x i) := by
  apply (φ₀).injective
  calc
    _ = φ₀ (projectiveConeFractionConstantHom x hgen (i.elim 1 x)) *
        φ₀ (algebraMap A₀ (FractionRing A₀) (projectiveConeCoordinate (E := E) x none)) := map_mul (φ₀) _ _
    _ = RatFunc.C (i.elim 1 x) * (RatFunc.C (1 : F) * RatFunc.X) :=
      congrArg₂ (· * ·) (projectiveConeFractionConstantHom_value x hgen _)
        (projectiveConeFractionEmbedding_coordinate x none)
    _ = RatFunc.C (i.elim 1 x) * RatFunc.X := by rw [map_one, one_mul]
    _ = φ₀ (algebraMap A₀ (FractionRing A₀) (projectiveConeCoordinate (E := E) x i)) :=
      (projectiveConeFractionEmbedding_coordinate x i).symm

end DimensionFourDependence
