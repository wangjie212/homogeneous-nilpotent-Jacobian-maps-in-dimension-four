import DimensionFourDependence.RationalSourceCurveField
import DimensionFourDependence.ClosedGaussParameterField

/-! # Finite relatively closed curve fields in the ternary rational source -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 1400000

variable {K : Type u} [Field K] [CharZero K] {n : ℕ}
local notation "R₀" => MvPolynomial (Fin n) K
local notation "F" => FractionRing R₀
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "F₄" => FractionRing R₄

/-- The checked source-line construction applies to any smaller set of
coordinates by adjoining unused independent coordinates. -/
theorem small_rational_source_fg_curve_field_rational
    (j : Fin n ↪ Fin 4) (L : IntermediateField K F)
    (hfg : L.FG) (hdim : Algebra.trdeg K L = 1) :
    Nonempty (RatFunc K ≃ₐ[K] L) := by
  let i : R₀ →ₐ[K] F₄ := (IsScalarTower.toAlgHom K R₄ F₄).comp (rename j)
  have hi : Function.Injective i :=
    (IsFractionRing.injective R₄ F₄).comp (rename_injective j j.injective)
  let g : F →ₐ[K] F₄ := IsFractionRing.liftAlgHom hi
  let e := IntermediateField.equivMap L g
  have hfg' : (L.map g).FG := by
    obtain ⟨s, hs, he⟩ := IntermediateField.fg_def.mp hfg
    exact IntermediateField.fg_def.mpr
      ⟨g '' s, hs.image g, by rw [← IntermediateField.adjoin_map, he]⟩
  have hdim' : Algebra.trdeg K (L.map g) = 1 := e.trdeg_eq.symm.trans hdim
  obtain ⟨q⟩ := rational_function_equiv_of_fg_curve_subfield (L.map g) hfg' hdim'
  exact ⟨q.trans e.symm⟩

/-- A finitely generated curve field in the actual rational source has
a finite, finitely generated, relatively closed rational extension
inside that source. -/
theorem small_rational_source_relative_closure_of_curve_is_rational
    (j : Fin n ↪ Fin 4) (B : IntermediateField K F)
    (hfg : B.FG) (hdim : Algebra.trdeg K B = 1) :
    Nonempty (RatFunc K ≃ₐ[K] ((algebraicClosure B F).restrictScalars K)) := by
  let E := algebraicClosure B F
  let L := E.restrictScalars K
  let : Algebra B L := (inferInstance : Algebra B E)
  let : IsScalarTower K B L := IsScalarTower.of_algebraMap_eq (by intro k; rfl)
  let : IsScalarTower B L F := IsScalarTower.of_algebraMap_eq (by intro b; rfl)
  let : Algebra.IsAlgebraic B L := (inferInstance : Algebra.IsAlgebraic B E)
  let : Algebra.EssFiniteType K F := rationalSource_essFiniteType
  let : Algebra.EssFiniteType B F := Algebra.EssFiniteType.of_comp K B F
  let : Module.Finite B L := algebraic_subextension_finite_of_essFiniteType (E := F)
  let : Algebra.EssFiniteType K B := IntermediateField.essFiniteType_iff.mpr hfg
  let : Algebra.EssFiniteType B L := inferInstance
  let : Algebra.EssFiniteType K L := Algebra.EssFiniteType.comp K B L
  let : FaithfulSMul K B :=
    (faithfulSMul_iff_algebraMap_injective K B).mpr (algebraMap K B).injective
  let : FaithfulSMul B L :=
    (faithfulSMul_iff_algebraMap_injective B L).mpr (algebraMap B L).injective
  have hl := trdeg_add_eq (A := L) K B
  rw [show Algebra.trdeg B L = 0 from trdeg_eq_zero, add_zero, hdim] at hl
  exact small_rational_source_fg_curve_field_rational j L
    (IntermediateField.essFiniteType_iff.mp inferInstance) hl.symm

end DimensionFourDependence
