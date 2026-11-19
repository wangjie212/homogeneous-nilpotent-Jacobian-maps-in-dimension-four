import DimensionFourDependence.CoefficientEuler
import DimensionFourDependence.RationalParameterDerivation

/-! # Coordinate differentiation in a full transcendence basis -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 1850000

variable {K F : Type u} [Field K] [CharZero K] [Field F] [Algebra K F] {n : ℕ}

/-- When a finite family is a full transcendence basis, its actual
relative closure is the whole source field. -/
noncomputable def fullBasisCoefficientEquiv (Y : Fin n → F)
    (hY : IsTranscendenceBasis K Y) : coefficientField (K := K) Y ≃ₐ[K] F := by
  let L := coefficientField (K := K) Y
  let : IsScalarTower K L F := coefficientFieldScalarTower Y
  let e : L →ₐ[K] F := IsScalarTower.toAlgHom K L F
  apply AlgEquiv.ofBijective e
  refine ⟨e.injective, ?_⟩
  intro a
  have ha : a ∈ L := mem_algebraicClosure_iff.mpr
    (IntermediateField.isAlgebraic_adjoin_iff.mpr (hY.isAlgebraic.isAlgebraic a))
  exact ⟨⟨a, ha⟩, rfl⟩

omit [CharZero K] in
theorem fullBasisCoefficientEquiv_apply (Y : Fin n → F)
    (hY : IsTranscendenceBasis K Y) (a : coefficientField (K := K) Y) :
    fullBasisCoefficientEquiv Y hY a = (a : F) := rfl

/-- The derivation with a specified unit value on one basis entry and
zero values on all the other basis entries. -/
noncomputable def fullBasisPartial (Y : Fin n → F) (hY : IsTranscendenceBasis K Y)
    (i : Fin n) : Derivation K F F :=
  fieldDerivationConjugate (fullBasisCoefficientEquiv Y hY) (coefficientPartial Y hY.1 i)

theorem fullBasisPartial_coordinate (Y : Fin n → F) (hY : IsTranscendenceBasis K Y)
    (i j : Fin n) : fullBasisPartial Y hY i (Y j) = if j = i then 1 else 0 := by
  change fullBasisPartial Y hY i (fullBasisCoefficientEquiv Y hY (coefficientCoordinate Y j)) = _
  rw [fullBasisPartial, fieldDerivationConjugate_apply,
    show coefficientPartial Y hY.1 i (coefficientCoordinate Y j) = _ from
      coefficientPartial_coordinate Y hY.1 i j]
  split <;> simp_all

theorem fullBasisPartials_commute (Y : Fin n → F) (hY : IsTranscendenceBasis K Y)
    (i j : Fin n) (a : F) :
    fullBasisPartial Y hY i (fullBasisPartial Y hY j a) =
      fullBasisPartial Y hY j (fullBasisPartial Y hY i a) := by
  obtain ⟨b, rfl⟩ := (fullBasisCoefficientEquiv Y hY).surjective a
  simp only [fullBasisPartial, fieldDerivationConjugate_apply, coefficientPartials_commute Y hY.1 i j]

/-- Derivations on the ambient field agree whenever they agree on the
entries of any full transcendence basis. -/
theorem fullBasis_derivation_ext (Y : Fin n → F) (hY : IsTranscendenceBasis K Y)
    (D E : Derivation K F F) (h : ∀ i, D (Y i) = E (Y i)) : D = E := by
  let L := coefficientField (K := K) Y
  let : IsScalarTower K L F := coefficientFieldScalarTower Y
  have he : D.compAlgebraMap L = E.compAlgebraMap L := by
    apply coefficient_ambient_derivation_ext Y
    intro i
    exact h i
  ext a
  obtain ⟨b, rfl⟩ := (fullBasisCoefficientEquiv Y hY).surjective a
  exact DFunLike.congr_fun he b

end DimensionFourDependence
