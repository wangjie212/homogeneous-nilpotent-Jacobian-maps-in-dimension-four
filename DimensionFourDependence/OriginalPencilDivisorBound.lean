import DimensionFourDependence.ProjectivePencilFiberDegree
import DimensionFourDependence.GaussImageDimension

/-! # The degree bound at an original divisor of the resolved pencil -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 4300000
set_option synthInstance.maxHeartbeats 135000

private theorem projectiveFieldPointIdeal_algHom_coordinates
    {k E F : Type u} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]
    (f : E →ₐ[k] F) (z : Fin 4 → E) :
    projectiveFieldPointIdeal (E := k) (f ∘ z) = projectiveFieldPointIdeal (E := k) z := by
  apply HomogeneousIdeal.toIdeal_injective
  ext P
  change projectiveFieldPointMap (E := k) (f ∘ z) P = 0 ↔ projectiveFieldPointMap (E := k) z P = 0
  have he (d : ℕ) : (projectiveFieldPointMap (E := k) (f ∘ z) P).coeff d =
      f ((projectiveFieldPointMap (E := k) z P).coeff d) := by
    rw [projectiveFieldPointMap_coeff, projectiveFieldPointMap_coeff]
    exact (comp_aeval_apply z f (homogeneousComponent d P)).symm
  constructor
  · intro h
    apply Polynomial.ext
    intro d
    apply f.injective
    change f ((projectiveFieldPointMap (E := k) z P).coeff d) = f ((0 : Polynomial E).coeff d)
    simp only [← he, h, Polynomial.coeff_zero, map_zero]
  · intro h
    apply Polynomial.ext
    intro d
    rw [he, h, Polynomial.coeff_zero, map_zero, Polynomial.coeff_zero]

variable {k : Type u} [Field k] [IsAlgClosed k]
local notation "P₃" => Proj (homogeneousSubmodule (Fin 4) k)
local notation "U" j:max => Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X j)

omit [IsAlgClosed k] in
private theorem projectivePullbackCoordinateAtDivisor_comp
    (Y Z : Scheme.{u}) (π : Y ⟶ Z) (α : Z ⟶ P₃) (y : Y)
    (a i : Fin 4) (ha : α (π y) ∈ U a) :
    projectivePullbackCoordinateAtDivisor Y (π ≫ α) y a i ha =
      π.stalkMap y (projectivePullbackCoordinateAtDivisor Z α (π y) a i ha) := by
  exact (Scheme.Hom.germ_stalkMap_apply π (α ⁻¹ᵁ U a) y ha
    (α.app (U a) (projectiveCoordinateRatioSection k a i))).symm

private theorem codimension_one_over_closed_pencil_value
    {B C : Scheme.{u}} [IsIntegral B] [IsIntegral C]
    (ψ : B ⟶ C) [IsDominant ψ] (hB : ∀ b : B, Order.coheight b ≤ 1)
    (b : B) (h : ψ b ≠ genericPoint C) : Order.coheight b = 1 := by
  have hne : b ≠ genericPoint B := by
    intro hb
    exact h (hb ▸ dominant_map_generic_point ψ)
  have hz : 0 < Order.coheight b := by
    apply Order.coheight_pos.mpr
    intro hm
    have hb : b ≤ genericPoint B := genericPoint_specializes b
    have hr : b ⤳ genericPoint B := hm hb
    exact hne (hr.antisymm (genericPoint_specializes b)).eq
  exact le_antisymm (hB b) (Order.one_le_iff_ne_zero.mpr hz.ne')

/-- The degree inequality of Lemma 4.4 at an original prime divisor over
the special pencil value. The resolved divisor retains the original
image ideal. The degree of the pushed-forward generic curve uses its
actual function-field degree over its projective image. -/
theorem lemma_4_4_at_original_pencil_divisor
    (Y Z B C : Scheme.{u}) [IsIntegral Y] [IsIntegral Z] [IsIntegral B] [IsIntegral C]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (π : Y ⟶ Z) [IsProper π] [IsDominant π] (hπ : Function.Surjective (dominantFunctionFieldHom π))
    (φ : Y ⟶ B) [IsDominant φ] (ψ : B ⟶ C) [IsDominant ψ]
    (zeroValue : C) (hzeroValue : zeroValue ≠ genericPoint C)
    (hB : ∀ b : B, Order.coheight b ≤ 1) (α : Z ⟶ P₃)
    (p : Z) (hp : Order.coheight p = 1) [IsIntegrallyClosed (Z.presheaf.stalk p)]
    (hzero : ∀ y : Y, π y = p → ψ (φ y) = zeroValue)
    (a : Fin 4) (ha : α p ∈ U a) (hnonempty : Nonempty ((π ≫ α) ⁻¹ᵁ U a))
    [Algebra k Z.functionField] [Algebra k Y.functionField] [Algebra k B.functionField]
    [Algebra k (Z.presheaf.stalk p)] [IsScalarTower k (Z.presheaf.stalk p) Z.functionField]
    (hπk : ∀ c : k, dominantFunctionFieldHom π (algebraMap k Z.functionField c) = algebraMap k Y.functionField c)
    (hφk : ∀ c : k, dominantFunctionFieldHom φ (algebraMap k B.functionField c) = algebraMap k Y.functionField c)
    (htr : Algebra.trdeg k B.functionField ≤ 1)
    {D D₀ : ℕ}
    (hD : letI := (dominantFunctionFieldHom φ).toAlgebra
      HasCurveHilbertDegree (projectiveFieldPointIdeal (E := B.functionField)
        (projectivePencilGenericCoordinate Y (π ≫ α) a hnonempty)).toIdeal D)
    (hD₀ : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := k)
      (fun i => IsLocalRing.residue (Z.presheaf.stalk p)
        (projectivePullbackCoordinateAtDivisor Z α p a i ha))).toIdeal D₀) :
    letI := (dominantFunctionFieldHom φ).toAlgebra
    let T := projectiveRatioField (K := B.functionField)
      (projectivePencilGenericCoordinate Y (π ≫ α) a hnonempty) a
    D₀ ≤ D ∧ (Module.Finite T Y.functionField → D₀ ≤ Module.finrank T Y.functionField * D) := by
  obtain ⟨y, hy, hy₁, hstalk⟩ := proper_birational_lifts_normal_divisor π hπ p hp
  have hby := codimension_one_over_closed_pencil_value ψ hB (φ y) (fun h => hzeroValue ((hzero y hy).symm.trans h))
  subst p
  let A := Z.presheaf.stalk (π y)
  let A' := Y.presheaf.stalk y
  let f := (π.stalkMap y).hom
  let : Algebra k A' := (f.comp (algebraMap k A)).toAlgebra
  let : IsIntegrallyClosed A' := IsIntegrallyClosed.of_equiv (RingEquiv.ofBijective f hstalk)
  let : IsScalarTower k A' Y.functionField := IsScalarTower.of_algebraMap_eq (R := k) (S := A')
    (A := Y.functionField) (fun c => by
      change algebraMap k Y.functionField c = algebraMap A' Y.functionField (f (algebraMap k A c))
      rw [← dominantFunctionFieldHom_stalk π, ← IsScalarTower.algebraMap_apply k A Z.functionField, hπk])
  let fr : IsLocalRing.ResidueField A →ₐ[k] IsLocalRing.ResidueField A' :=
    { IsLocalRing.ResidueField.map f with
      commutes' := by
        intro c
        change IsLocalRing.ResidueField.map f (IsLocalRing.residue A (algebraMap k A c)) =
          IsLocalRing.residue A' (f (algebraMap k A c))
        exact IsLocalRing.ResidueField.map_residue f _ }
  let w := fun i => IsLocalRing.residue A (projectivePullbackCoordinateAtDivisor Z α (π y) a i ha)
  let z := fun i => IsLocalRing.residue A' (projectivePullbackCoordinateAtDivisor Y (π ≫ α) y a i ha)
  have he : fr ∘ w = z := by
    funext i
    change IsLocalRing.ResidueField.map f (IsLocalRing.residue A
      (projectivePullbackCoordinateAtDivisor Z α (π y) a i ha)) = _
    rw [IsLocalRing.ResidueField.map_residue]
    exact congrArg (IsLocalRing.residue A') (projectivePullbackCoordinateAtDivisor_comp Y Z π α y a i ha).symm
  have hspecial : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := k) z).toIdeal D₀ := by
    rw [← he, projectiveFieldPointIdeal_algHom_coordinates fr w]
    exact hD₀
  have hle := projective_pencil_fiber_divisor_image_degree_le_generic Y B φ (π ≫ α) y hy₁ hby a hnonempty
    ha hφk htr hD hspecial
  let : Algebra B.functionField Y.functionField := (dominantFunctionFieldHom φ).toAlgebra
  let T := projectiveRatioField (K := B.functionField) (projectivePencilGenericCoordinate Y (π ≫ α) a hnonempty) a
  refine ⟨hle, ?_⟩
  intro hfin
  let : Module.Finite T Y.functionField := hfin
  have hpos : 1 ≤ Module.finrank T Y.functionField := Module.finrank_pos
  exact hle.trans (by simpa only [one_mul] using Nat.mul_le_mul_right D hpos)

end DimensionFourDependence
