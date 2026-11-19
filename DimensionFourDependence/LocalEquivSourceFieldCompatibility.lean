import DimensionFourDependence.LocalEquivUnramifiedSource

/-! # The rational order map is the original source-function pullback

The constructed rational map agrees on every original source function.
When the original source field is the fraction field of that ring, this
characterizes the pullback uniquely, independently of the local model.
-/

namespace DimensionFourDependence

variable {R O A B F : Type*} [CommRing R]
  [CommRing O] [IsDomain O] [CommRing A] [IsDomain A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra R O] [Algebra R A] [Algebra R B] [Algebra O B] [IsScalarTower R O B]
  [Module.IsTorsionFree O B] [Field F] [Algebra O F] [IsFractionRing O F]
  [Algebra R F] [IsScalarTower R O F]

/-- The normalization's constructed rational source map preserves the
original source-ring values, not merely the abstract source DVR. -/
theorem localEquivSourceFractionHom_original_source (e : A ≃ₐ[R] B) (r : R) :
    letI : Algebra O A := localEquivSourceAlgebra (O := O) e
    localEquivSourceFractionHom (O := O) (F := F) e (algebraMap R F r) =
      algebraMap A (FractionRing A) (algebraMap R A r) := by
  let : Algebra O A := localEquivSourceAlgebra (O := O) e
  rw [IsScalarTower.algebraMap_apply R O F, localEquivSourceFractionHom_algebraMap,
    localEquivSourceAlgHom_original_source]

variable [IsDomain R] [IsFractionRing R F]

omit [IsDomain R] in
/-- The rational source map equals any given geometric pullback with
the same original source values. Thus the order comparison is independent
of the choice of the unramified local model. -/
theorem localEquivSourceFractionHom_eq_of_original_source (e : A ≃ₐ[R] B)
    (j : F →+* FractionRing A)
    (hj : ∀ r : R, j (algebraMap R F r) = algebraMap A (FractionRing A) (algebraMap R A r)) :
    letI : Algebra O A := localEquivSourceAlgebra (O := O) e
    (localEquivSourceFractionHom (O := O) (F := F) e).toRingHom = j := by
  let : Algebra O A := localEquivSourceAlgebra (O := O) e
  apply IsFractionRing.ringHom_ext (A := R)
  intro r
  exact (localEquivSourceFractionHom_original_source (O := O) (F := F) e r).trans (hj r).symm

end DimensionFourDependence
