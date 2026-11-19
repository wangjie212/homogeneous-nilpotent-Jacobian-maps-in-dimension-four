import DimensionFourDependence.CoefficientResidueCurveDegreeExistence
import DimensionFourDependence.ProjectivePointCoefficientRestriction
import DimensionFourDependence.ProjectivePullbackRationalCoordinates
import DimensionFourDependence.NormalDivisorStalkDvr

/-! # Degree of the image of a vertical divisor of a pencil -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v
set_option maxHeartbeats 3700000
set_option synthInstance.maxHeartbeats 115000

private theorem projective_hilbert_function_of_bijective_scalar_map
    {k L F : Type u} {σ : Type v} [Field k] [Field L] [Field F] [Finite σ]
    [Algebra k L] [Algebra k F] [Algebra L F] [IsScalarTower k L F]
    (hs : Function.Surjective (algebraMap k L)) (z : σ → F) (n : ℕ) :
    projectiveHilbertFunction (projectiveFieldPointIdeal (E := L) z).toIdeal n =
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := k) z).toIdeal n := by
  let f := MvPolynomial.map (algebraMap k L) (σ := σ)
  have hmap : Function.Surjective f := MvPolynomial.map_surjective _ hs
  have he : extendCoefficientIdeal L (projectiveFieldPointIdeal (E := k) z).toIdeal =
      (projectiveFieldPointIdeal (E := L) z).toIdeal := by
    rw [extendCoefficientIdeal, ← projectiveFieldPointIdeal_coefficient_comap (E := L),
      Ideal.map_comap_of_surjective _ hmap]
  rw [← he, projectiveHilbertFunction_field_extension]

/-- A nonzero local pencil zero over a curve forces the restricted
coefficient residue to be algebraic. Over algebraically closed constants
the special Hilbert function is therefore computed over the original field. -/
theorem pencil_zero_divisor_projective_hilbert_bound
    {k C F A : Type u} {σ : Type v} [Field k] [IsAlgClosed k] [Field C] [Field F] [Finite σ]
    [CommRing A] [IsDomain A] [ValuationRing A] [Algebra k A] [Algebra A F] [IsFractionRing A F]
    [Algebra k C] [Algebra C F] [Algebra k F] [IsScalarTower k A F] [IsScalarTower k C F]
    (htr : Algebra.trdeg k C ≤ 1) (c : C) (t : A) (ht : t ≠ 0)
    (ht₀ : t ∈ IsLocalRing.maximalIdeal A) (htC : algebraMap A F t = algebraMap C F c)
    (z : σ → A) (n : ℕ) :
    projectiveHilbertFunction (projectiveFieldPointIdeal (E := k) (fun i => IsLocalRing.residue A (z i))).toIdeal n ≤
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := C) (fun i => algebraMap A F (z i))).toIdeal n := by
  let V := coefficientRestrictionValuationSubring (A := A) (F := F) C
  let : Algebra k V := coefficientRestrictionConstantAlgebra (A := A) (F := F) C k
  let : Algebra (IsLocalRing.ResidueField V) (IsLocalRing.ResidueField A) :=
    coefficientRestrictionResidueAlgebra (A := A) (F := F) C
  let : IsScalarTower k (IsLocalRing.ResidueField V) (IsLocalRing.ResidueField A) :=
    coefficientRestrictionResidueAlgebra_constant_scalarTower (E := k) (A := A) (F := F) C
  let : Algebra.IsAlgebraic k (IsLocalRing.ResidueField V) :=
    source_valuation_coefficient_restriction_curve_residue_isAlgebraic (A := A) (F := F) C k c t ht ht₀ htC htr
  have hs : Function.Surjective (algebraMap k (IsLocalRing.ResidueField V)) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := IsLocalRing.ResidueField V)).2
  rw [← projective_hilbert_function_of_bijective_scalar_map hs]
  exact source_valuation_coefficient_restriction_hilbert_bound C z n

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The exact original coordinate ratio pulled back to the stalk of a
point of the actual inverse projective chart. -/
noncomputable def projectivePullbackCoordinateAtDivisor
    (Y : Scheme.{u}) (f : Y ⟶ Proj (homogeneousSubmodule (Fin 4) k)) (p : Y)
    (a i : Fin 4) (ha : f p ∈ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X a)) :
    Y.presheaf.stalk p :=
  let U := Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X a)
  Y.presheaf.germ (f ⁻¹ᵁ U) p ha (f.app U (projectiveCoordinateRatioSection k a i))

/-- The generic ratio in the chosen projective chart containing the image
of the divisor. Only this single coordinate chart has to be nonempty. -/
noncomputable def projectivePencilGenericCoordinate
    (Y : Scheme.{u}) [IsIntegral Y] (f : Y ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    (a : Fin 4) (hU : Nonempty (f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X a)))
    (i : Fin 4) : Y.functionField :=
  Y.germToFunctionField (f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X a))
    (f.app (Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X a)) (projectiveCoordinateRatioSection k a i))

/-- At a normal codimension-one point with a nonzero regular pencil
zero, the actual projective image of the divisor has degree at most
the projective image of the generic curve. The generic and special
coordinates are the pullbacks by the very same morphism. -/
theorem projective_pencil_divisor_image_degree_le_generic
    (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : Y ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    (p : Y) (hp : Order.coheight p = 1) [IsIntegrallyClosed (Y.presheaf.stalk p)]
    (a : Fin 4) (hU : Nonempty (f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X a)))
    (ha : f p ∈ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X a))
    (C : Type u) [Field C] [Algebra k C] [Algebra C Y.functionField] [Algebra k Y.functionField]
    [Algebra k (Y.presheaf.stalk p)] [IsScalarTower k C Y.functionField]
    [IsScalarTower k (Y.presheaf.stalk p) Y.functionField]
    (htr : Algebra.trdeg k C ≤ 1) (c : C) (t : Y.presheaf.stalk p) (ht : t ≠ 0)
    (ht₀ : t ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk p))
    (htC : algebraMap (Y.presheaf.stalk p) Y.functionField t = algebraMap C Y.functionField c)
    {D D₀ : ℕ} (hD : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := C)
      (projectivePencilGenericCoordinate Y f a hU)).toIdeal D)
    (hD₀ : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := k)
      (fun i => IsLocalRing.residue (Y.presheaf.stalk p) (projectivePullbackCoordinateAtDivisor Y f p a i ha))).toIdeal D₀) :
    D₀ ≤ D := by
  let : IsDiscreteValuationRing (Y.presheaf.stalk p) := normal_codimension_one_scheme_stalk_isDVR p hp
  let z := fun i => projectivePullbackCoordinateAtDivisor Y f p a i ha
  let : Nonempty (f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X a)) := hU
  have hz : (fun i => algebraMap (Y.presheaf.stalk p) Y.functionField (z i)) =
      projectivePencilGenericCoordinate Y f a hU := by
    funext i
    exact Scheme.algebraMap_germ_eq_germToFunctionField Y ha _
  apply curveHilbertDegree_le_of_hilbertFunction_le _ _ ?_ hD hD₀
  intro n
  have h := pencil_zero_divisor_projective_hilbert_bound htr c t ht ht₀ htC z n
  rwa [hz] at h

end DimensionFourDependence
