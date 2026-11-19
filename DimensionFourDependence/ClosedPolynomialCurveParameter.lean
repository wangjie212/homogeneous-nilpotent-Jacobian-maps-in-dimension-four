import DimensionFourDependence.ClosedRationalSourceCurveField
import DimensionFourDependence.PolynomialSourceRationalFieldIntersection
import DimensionFourDependence.RationalParameterCoefficientAlgebraicity

/-! # A common closed polynomial parameter for a curve of polynomial outputs -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 1800000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K] {n m : ℕ}
local notation "R₀" => MvPolynomial (Fin n) K
local notation "F" => FractionRing R₀
local notation "ι" => (algebraMap R₀ F)

/-- A finite polynomial family of output transcendence degree one
has a common nonconstant polynomial parameter generating the entire
relative algebraic closure of its output field. -/
theorem polynomial_curve_outputs_have_common_closed_polynomial_parameter
    (j : Fin n ↪ Fin 4) (H : Fin m → R₀)
    (htr : Algebra.trdeg K (IntermediateField.adjoin K (Set.range (fun i => ι (H i)))) = 1) :
    ∃ (T : R₀) (A : Fin m → Polynomial K), 0 < T.totalDegree ∧
      (∀ i, H i = Polynomial.aeval T (A i)) ∧
      IntermediateField.adjoin K {ι T} =
        (algebraicClosure (IntermediateField.adjoin K (Set.range (fun i => ι (H i)))) F).restrictScalars K := by
  let B := IntermediateField.adjoin K (Set.range (fun i => ι (H i)))
  let L := (algebraicClosure B F).restrictScalars K
  have hfg : B.FG := IntermediateField.fg_adjoin_of_finite (Set.finite_range _)
  obtain ⟨e⟩ := small_rational_source_relative_closure_of_curve_is_rational j B hfg htr
  let f := L.val.comp e.toAlgHom
  have hf : f.fieldRange = L := by
    ext z
    constructor
    · rintro ⟨r, rfl⟩
      exact (e r).property
    · intro hz
      obtain ⟨r, hr⟩ := e.surjective ⟨z, hz⟩
      exact ⟨r, congrArg Subtype.val hr⟩
  have hB (i : Fin m) : ι (H i) ∈ B := IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
  have hL (i : Fin m) : ι (H i) ∈ L := by
    change ι (H i) ∈ algebraicClosure B F
    exact mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (A := F) (⟨ι (H i), hB i⟩ : B))
  have hnonconstant : ∃ i, ¬ ∃ c : K, ι (H i) = algebraMap K F c := by
    by_contra h
    push Not at h
    have hbot : B = ⊥ := by
      apply bot_unique
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨i, rfl⟩
      obtain ⟨c, hc⟩ := h i
      change ι (H i) ∈ (⊥ : IntermediateField K F)
      rw [hc]
      exact (⊥ : IntermediateField K F).algebraMap_mem c
    have hz : Algebra.trdeg K B = 0 := by
      rw [hbot]
      exact trdeg_eq_zero
    exact one_ne_zero (htr.symm.trans hz)
  obtain ⟨i, hi⟩ := hnonconstant
  have hi' : ι (H i) ∈ f.fieldRange := hf.symm ▸ hL i
  obtain ⟨r, hr⟩ := hi'
  change f r = ι (H i) at hr
  obtain ⟨g, T, hg, hT⟩ := rational_curve_field_with_regular_value_has_regular_generator f r (H i)
    hr (by simpa only [hr] using hi)
  have hgL : g.fieldRange = L := hg.trans hf
  have hA (k : Fin m) : ∃ A : Polynomial K, H k = Polynomial.aeval T A := by
    have hk : ι (H k) ∈ g.fieldRange := hgL.symm ▸ hL k
    obtain ⟨q, hq⟩ := hk
    obtain ⟨P, hP⟩ := polynomial_source_value_lies_in_polynomial_parameter_ring g T hT q (H k) hq
    exact ⟨P, hP.symm⟩
  choose A hA using hA
  have hdeg : 0 < T.totalDegree := by
    by_contra h
    have hC : T = C (T.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_not_pos h)
    have hscalar : g RatFunc.X = algebraMap K F (T.coeff 0) := calc
      _ = ι T := hT.symm
      _ = ι (C (T.coeff 0)) := congrArg (ι) hC
      _ = _ := by rw [← algebraMap_eq, ← IsScalarTower.algebraMap_apply K R₀ F]
    have halg : IsAlgebraic K (g RatFunc.X) := by rw [hscalar]; exact isAlgebraic_algebraMap _
    exact RatFunc.transcendental_X ((isAlgebraic_algHom_iff g g.injective).mp halg)
  exact ⟨T, A, hdeg, hA, (congrArg (fun a : F => IntermediateField.adjoin K {a}) hT).trans
    ((rational_parameter_hom_fieldRange g).trans hgL)⟩

end DimensionFourDependence
