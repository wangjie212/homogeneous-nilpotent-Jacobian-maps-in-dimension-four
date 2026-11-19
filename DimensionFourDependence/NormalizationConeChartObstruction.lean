import DimensionFourDependence.ProjectiveChartFunctionField
import DimensionFourDependence.NormalizationRing
import Mathlib.RingTheory.Localization.AsSubring

/-! # An integral inverse chart coefficient cannot coexist with a nonvertex cone zero -/

namespace DimensionFourDependence

/-- A common nonzero radial factor cancels from every original
projective coordinate ratio, with the original field map retained. -/
theorem common_radial_coordinate_ratios
    {F L σ : Type*} [Field F] [Field L] (ψ : F →+* L)
    (w : σ → F) (z : σ → L) (t : L) (ht : t ≠ 0)
    (hcoords : ∀ i, ψ (w i) * t = z i) (a : σ) (ha : w a ≠ 0) (i : σ) :
    ψ (w i / w a) = z i / z a := by
  rw [map_div₀, ← hcoords i, ← hcoords a]
  have hwa := (map_ne_zero ψ).mpr ha
  field_simp

variable {E F A : Type*} [Field E] [Field F] [Algebra E F]
  [CommRing A] [IsDomain A] [Algebra E A]

/-- At any prime of the actual normalization, a cone element cannot
vanish while an original homogeneous coordinate is a unit and its
corresponding inverse chart coefficient is integral. The whole original
ratio algebra maps into the actual prime-local regular subalgebra. -/
theorem normalization_cone_zero_excludes_integral_inverse_chart_coefficient
    (Q : Ideal (normalizationRing A)) [Q.IsPrime]
    (ψ : F →ₐ[E] FractionRing A) (w : Fin 4 → F) (z : Fin 4 → A)
    (a : Fin 4) (b : normalizationRing A) (u : F)
    (hb : b ∈ Q) (ha : algebraMap A (normalizationRing A) (z a) ∉ Q)
    (hratios : ∀ i, ψ (w i / w a) =
      algebraMap A (FractionRing A) (z i) / algebraMap A (FractionRing A) (z a))
    (hprod : (b : FractionRing A) * ψ (w a / u) = algebraMap A (FractionRing A) (z a)) :
    ¬ IsIntegral (projectiveCoordinateChartAlgebra (C := E) w a) (w a / u) := by
  intro hi
  let B := normalizationRing A
  let L := FractionRing A
  let : IsFractionRing B L := normalizationRing_isFractionRing A
  let : IsIntegrallyClosed B := normalizationRing_isIntegrallyClosed A
  let T : Subalgebra B L := Localization.subalgebra.ofField L Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  let : IsIntegrallyClosed T :=
    isIntegrallyClosed_of_isLocalization T Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  let : IsLocalRing T := IsLocalization.AtPrime.isLocalRing T Q
  let S := projectiveCoordinateChartAlgebra (C := E) w a
  have hle : S ≤ (T.restrictScalars E).comap ψ := by
    apply Algebra.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    change ψ (w i / w a) ∈ T
    change ∃ (v s : B) (_ : s ∈ Q.primeCompl),
      ψ (w i / w a) = algebraMap B L v * (algebraMap B L s)⁻¹
    refine ⟨algebraMap A B (z i), algebraMap A B (z a), ha, ?_⟩
    exact (hratios i).trans (by
      rw [IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A B L]
      rfl)
  let f : S →+* T := (ψ.toRingHom.comp S.val.toRingHom).codRestrict T.toSubring (fun s => hle s.property)
  have hcomp : (algebraMap T L).comp f = ψ.toRingHom.comp S.val.toRingHom := by
    apply RingHom.ext
    intro s
    rfl
  have hint : IsIntegral T (ψ (w a / u)) := hi.map_of_comp_eq f ψ.toRingHom hcomp
  obtain ⟨v, hv⟩ := (IsIntegrallyClosed.isIntegral_iff (R := T) (K := L)).mp hint
  have he : algebraMap B T b * v = algebraMap B T (algebraMap A B (z a)) := by
    apply Subtype.ext
    change (b : L) * (v : L) = algebraMap A L (z a)
    exact (congrArg (fun y : L => (b : L) * y) hv).trans hprod
  have hbT : algebraMap B T b ∈ IsLocalRing.maximalIdeal T :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff T Q b).mpr hb
  have haT : algebraMap B T (algebraMap A B (z a)) ∈ IsLocalRing.maximalIdeal T :=
    he ▸ (IsLocalRing.maximalIdeal T).mul_mem_right v hbT
  exact ha ((IsLocalization.AtPrime.to_map_mem_maximal_iff T Q _).mp haT)

end DimensionFourDependence
