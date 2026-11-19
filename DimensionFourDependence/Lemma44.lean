import DimensionFourDependence.OriginalPencilDivisorBound
import DimensionFourDependence.SchemeSectionVanishingDivisor
import DimensionFourDependence.ProjectivePrimeCoordinates

/-! # Lemma 4.4 by specialization of the actual projective image -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 5500000
set_option synthInstance.maxHeartbeats 135000

variable {k : Type u} [Field k] [IsAlgClosed k]
local notation "G" => homogeneousSubmodule (Fin 4) k
local notation "P₃" => Proj G
local notation "U" a:max => Proj.basicOpen G (X a)

/-- Local vanishing for a hyperplane-pencil section, given by its
regular coefficient in the indicated pullback coordinate frame. -/
def projectivePencilSectionZeroAt {Z : Scheme.{u}} (α : Z ⟶ P₃)
    (s : ∀ a : Fin 4, Γ(Z, α ⁻¹ᵁ U a)) (p : Z) (a : Fin 4) (ha : α p ∈ U a) : Prop :=
  Z.presheaf.germ (α ⁻¹ᵁ U a) p ha (s a) ∈ maximalIdeal (Z.presheaf.stalk p)

/-- Lemma 4.4 in the projective coordinate frames. The degree of the
pulled-back hyperplane on the generic curve is the degree of the
projective image multiplied by its actual generic mapping degree. The
resolution agrees with the pencil wherever at least one section is
nonvanishing. The common special image is specified by its complete
projective ideal. The proof constructs an original prime divisor over
the special value and then specializes the projective image. -/
theorem lemma_4_4
    (Y Z B C : Scheme.{u}) [IsIntegral Y] [IsIntegral Z] [IsIntegral B] [IsIntegral C]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (π : Y ⟶ Z) [IsProper π] [IsDominant π] (hπ : Function.Surjective (dominantFunctionFieldHom π))
    (φ : Y ⟶ B) [IsDominant φ] (ψ : B ⟶ C) [IsDominant ψ] [IsProper (φ ≫ ψ)]
    (zeroValue : C) (hzeroValue : zeroValue ≠ genericPoint C)
    (hB : ∀ b : B, Order.coheight b ≤ 1) (α : Z ⟶ P₃)
    (s₀ s₁ : ∀ a : Fin 4, Γ(Z, α ⁻¹ᵁ U a))
    (hs₀ : ∀ a, Nonempty (α ⁻¹ᵁ U a) → s₀ a ≠ 0)
    (hnormal : ∀ p : Z, Order.coheight p = 1 → IsIntegrallyClosed (Z.presheaf.stalk p))
    (hnocommon : ∀ (p : Z) (_hp : Order.coheight p = 1) (a : Fin 4) (ha : α p ∈ U a),
      projectivePencilSectionZeroAt α s₀ p a ha → ¬ projectivePencilSectionZeroAt α s₁ p a ha)
    (hresolve : ∀ (y : Y) (a : Fin 4) (ha : α (π y) ∈ U a),
      (¬ projectivePencilSectionZeroAt α s₀ (π y) a ha ∨ ¬ projectivePencilSectionZeroAt α s₁ (π y) a ha) →
      (ψ (φ y) = zeroValue ↔ projectivePencilSectionZeroAt α s₀ (π y) a ha))
    [Algebra k Z.functionField] [Algebra k Y.functionField] [Algebra k B.functionField]
    (aZ : ∀ p : Z, Algebra k (Z.presheaf.stalk p))
    (htower : ∀ p : Z, letI := aZ p; IsScalarTower k (Z.presheaf.stalk p) Z.functionField)
    (hπk : ∀ c : k, dominantFunctionFieldHom π (algebraMap k Z.functionField c) = algebraMap k Y.functionField c)
    (hφk : ∀ c : k, dominantFunctionFieldHom φ (algebraMap k B.functionField c) = algebraMap k Y.functionField c)
    (htr : Algebra.trdeg k B.functionField ≤ 1)
    (C₀ : ProjectiveSpectrum G) (δ D₀ : ℕ) (hD₀ : HasCurveHilbertDegree C₀.asHomogeneousIdeal.toIdeal D₀)
    (himage : ∀ (p : Z) (_hp : Order.coheight p = 1) (a : Fin 4) (ha : α p ∈ U a),
      projectivePencilSectionZeroAt α s₀ p a ha →
      letI := aZ p
      projectiveFieldPointIdeal (E := k) (fun i => IsLocalRing.residue (Z.presheaf.stalk p)
        (projectivePullbackCoordinateAtDivisor Z α p a i ha)) = C₀.asHomogeneousIdeal)
    (hδ : ∀ (a : Fin 4) (hU : Nonempty ((π ≫ α) ⁻¹ᵁ U a)),
      letI := (dominantFunctionFieldHom φ).toAlgebra
      let x := projectivePencilGenericCoordinate Y (π ≫ α) a hU
      let T := projectiveRatioField (K := B.functionField) x a
      ∃ D : ℕ, HasCurveHilbertDegree (projectiveFieldPointIdeal (E := B.functionField) x).toIdeal D ∧
        Module.Finite T Y.functionField ∧ δ = Module.finrank T Y.functionField * D) :
    D₀ ≤ δ := by
  let τ := φ ≫ ψ
  have hclosed : IsClosed (Set.range τ) := τ.isClosedMap.isClosed_range
  have htop := τ.denseRange.closure_range
  rw [hclosed.closure_eq] at htop
  have hmem : zeroValue ∈ Set.range τ := by rw [htop]; trivial
  obtain ⟨y₀, hy₀⟩ := hmem
  change ψ (φ y₀) = zeroValue at hy₀
  obtain ⟨a, ha₀⟩ := projectiveSpectrum_exists_coordinate_not_mem (α (π y₀))
  have ha : α (π y₀) ∈ U a := ha₀
  have hvan : projectivePencilSectionZeroAt α s₀ (π y₀) a ha := by
    by_contra hv
    exact hv ((hresolve y₀ a ha (Or.inl hv)).mp hy₀)
  obtain ⟨p, hpU, _hsp, hp, hp₀⟩ := scheme_regular_section_zero_has_prime_divisor Z (α ⁻¹ᵁ U a)
    (s₀ a) (hs₀ a ⟨⟨π y₀, ha⟩⟩) (π y₀) ha hvan
  have hz : ∀ y : Y, π y = p → ψ (φ y) = zeroValue := by
    intro y hy
    subst p
    exact (hresolve y a hpU (Or.inr (hnocommon (π y) hp a hpU hp₀))).mpr hp₀
  let : Algebra k (Z.presheaf.stalk p) := aZ p
  let : IsIntegrallyClosed (Z.presheaf.stalk p) := hnormal p hp
  let : IsScalarTower k (Z.presheaf.stalk p) Z.functionField := htower p
  have hU : Nonempty ((π ≫ α) ⁻¹ᵁ U a) := ⟨⟨y₀, ha⟩⟩
  obtain ⟨D, hD, hfin, he⟩ := hδ a hU
  have hspecial : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := k)
      (fun i => IsLocalRing.residue (Z.presheaf.stalk p)
        (projectivePullbackCoordinateAtDivisor Z α p a i hpU))).toIdeal D₀ := by
    rw [himage p hp a hpU hp₀]
    exact hD₀
  have hle := lemma_4_4_at_original_pencil_divisor Y Z B C π hπ φ ψ zeroValue hzeroValue hB α
    p hp hz a hpU hU hπk hφk htr hD hspecial
  exact he ▸ hle.2 hfin

end DimensionFourDependence
