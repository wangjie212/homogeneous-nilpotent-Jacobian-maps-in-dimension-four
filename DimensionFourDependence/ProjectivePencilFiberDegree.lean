import DimensionFourDependence.PencilDivisorCurveDegree
import DimensionFourDependence.ProperBirationalDivisorLift

/-! # Relative projective degree at a divisor over a pencil fiber -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 3300000
set_option synthInstance.maxHeartbeats 125000

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A dominant morphism to an integral base curve supplies its own
nonzero local pencil zero at each divisor over a codimension-one point
of the base. The degree comparison uses the base function field and the
same projective morphism on the generic fiber and the divisor. -/
theorem projective_pencil_fiber_divisor_image_degree_le_generic
    (Y B : Scheme.{u}) [IsIntegral Y] [IsIntegral B] [IsLocallyNoetherian Y]
    (φ : Y ⟶ B) [IsDominant φ]
    (f : Y ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    (p : Y) (hp : Order.coheight p = 1) [IsIntegrallyClosed (Y.presheaf.stalk p)]
    (hb : Order.coheight (φ p) = 1)
    (a : Fin 4) (hU : Nonempty (f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X a)))
    (ha : f p ∈ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X a))
    [Algebra k B.functionField] [Algebra k Y.functionField]
    [Algebra k (Y.presheaf.stalk p)] [IsScalarTower k (Y.presheaf.stalk p) Y.functionField]
    (hφ : ∀ c : k, dominantFunctionFieldHom φ (algebraMap k B.functionField c) = algebraMap k Y.functionField c)
    (htr : Algebra.trdeg k B.functionField ≤ 1)
    {D D₀ : ℕ}
    (hD : letI := (dominantFunctionFieldHom φ).toAlgebra
      HasCurveHilbertDegree (projectiveFieldPointIdeal (E := B.functionField)
        (projectivePencilGenericCoordinate Y f a hU)).toIdeal D)
    (hD₀ : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := k)
      (fun i => IsLocalRing.residue (Y.presheaf.stalk p)
        (projectivePullbackCoordinateAtDivisor Y f p a i ha))).toIdeal D₀) : D₀ ≤ D := by
  let A := B.presheaf.stalk (φ p)
  let C := B.functionField
  have hdim : ringKrullDim A = 1 := (ringKrullDim_stalk_eq_coheight (φ p)).trans (by rw [hb]; rfl)
  have hnf : ¬ IsField A := by
    intro hf
    let : Field A := hf.toField
    have hzero : ringKrullDim A ≤ 0 := Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 0 A)
    rw [hdim] at hzero
    norm_num at hzero
  have hne : IsLocalRing.maximalIdeal A ≠ ⊥ := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hnf
  have hs₁ : ∃ s : A, s ∈ IsLocalRing.maximalIdeal A ∧ s ≠ 0 := by
    by_contra! hz
    exact hne (le_antisymm (fun s hs => Ideal.mem_bot.mpr (hz s hs)) bot_le)
  obtain ⟨s, hs, hs₀⟩ := hs₁
  let t := (φ.stalkMap p).hom s
  let c := algebraMap A C s
  let : Algebra C Y.functionField := (dominantFunctionFieldHom φ).toAlgebra
  let : IsScalarTower k C Y.functionField := IsScalarTower.of_algebraMap_eq (fun c => (hφ c).symm)
  have htC : algebraMap (Y.presheaf.stalk p) Y.functionField t = algebraMap C Y.functionField c :=
    (dominantFunctionFieldHom_stalk φ p s).symm
  have ht : t ≠ 0 := by
    intro hz
    apply hs₀
    apply IsFractionRing.injective A C
    apply (dominantFunctionFieldHom φ).injective
    change algebraMap C Y.functionField c = _
    rw [← htC, hz, map_zero]
    rw [map_zero (algebraMap A C), map_zero (dominantFunctionFieldHom φ)]
  have ht₀ : t ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk p) := by
    intro hu
    exact hs (isUnit_of_map_unit (φ.stalkMap p).hom s hu)
  exact projective_pencil_divisor_image_degree_le_generic Y f p hp a hU ha C htr c t ht ht₀ htC hD hD₀

/-- A positive generic mapping degree scales the generic projective
image degree to the degree of the pushed-forward generic curve. The
special projective image degree is bounded by this scaled degree. -/
theorem projective_pencil_fiber_divisor_degree_le_generic_pushforward
    (Y B : Scheme.{u}) [IsIntegral Y] [IsIntegral B] [IsLocallyNoetherian Y]
    (φ : Y ⟶ B) [IsDominant φ]
    (f : Y ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    (p : Y) (hp : Order.coheight p = 1) [IsIntegrallyClosed (Y.presheaf.stalk p)]
    (hb : Order.coheight (φ p) = 1)
    (a : Fin 4) (hU : Nonempty (f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X a)))
    (ha : f p ∈ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X a))
    [Algebra k B.functionField] [Algebra k Y.functionField]
    [Algebra k (Y.presheaf.stalk p)] [IsScalarTower k (Y.presheaf.stalk p) Y.functionField]
    (hφ : ∀ c : k, dominantFunctionFieldHom φ (algebraMap k B.functionField c) = algebraMap k Y.functionField c)
    (htr : Algebra.trdeg k B.functionField ≤ 1)
    {D D₀ m : ℕ}
    (hD : letI := (dominantFunctionFieldHom φ).toAlgebra
      HasCurveHilbertDegree (projectiveFieldPointIdeal (E := B.functionField)
        (projectivePencilGenericCoordinate Y f a hU)).toIdeal D)
    (hD₀ : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := k)
      (fun i => IsLocalRing.residue (Y.presheaf.stalk p)
        (projectivePullbackCoordinateAtDivisor Y f p a i ha))).toIdeal D₀)
    (hm : 0 < m) : D₀ ≤ m * D :=
  (projective_pencil_fiber_divisor_image_degree_le_generic Y B φ f p hp hb a hU ha hφ htr hD hD₀).trans
    (by simpa only [one_mul] using Nat.mul_le_mul_right D (show 1 ≤ m from hm))

end DimensionFourDependence
