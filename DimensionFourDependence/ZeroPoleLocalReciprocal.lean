import DimensionFourDependence.Defs
import Mathlib.RingTheory.Valuation.LocalSubring

/-! # A zero and a pole meeting in a local ring

If two valuation overrings of a local subring see a zero and a pole
of the same rational function, the reciprocal of any translated level
cannot belong to that local ring. The valuations need only contain
the local ring: their centers may be different branch primes below
its maximal ideal. No normality or divisor-closure assertion is used.
-/

namespace DimensionFourDependence

variable {A kZero kPole : Type*} [CommRing A] [IsLocalRing A]
  [Field kZero] [Field kPole]

/-- Residue specializations of a putative regular reciprocal at a
zero branch and a pole branch contradict locality. -/
theorem local_reciprocal_zero_pole_specializations_impossible
    (φ : A →+* kZero) (ψ : A →+* kPole) (u c : A)
    (hzero : φ u * (-φ c) = 1) (hpole : ψ u = 0) : False := by
  have hu : u ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro h
    have hmap := h.map ψ
    rw [hpole] at hmap
    exact not_isUnit_zero hmap
  have hv : c * u + 1 ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro h
    have he : φ (c * u + 1) = 0 := by
      simp only [map_add, map_mul, map_one]
      linear_combination -hzero
    have hmap := h.map φ
    rw [he] at hmap
    exact not_isUnit_zero hmap
  have hone : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    simpa only [add_sub_cancel_left] using
      (IsLocalRing.maximalIdeal A).sub_mem hv
        ((IsLocalRing.maximalIdeal A).mul_mem_left c hu)
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)

variable {F : Type*} [Field F]

/-- A local ring cannot contain a level reciprocal when valuation
branches through its closed point see respectively a zero and a pole.
Only containment, rather than domination, is required for the branch
valuations. -/
theorem zero_pole_level_reciprocal_not_mem_local_subring
    (R : LocalSubring F) (f c : F) (hc : c ∈ R.toSubring)
    (V₀ Vinf : ValuationSubring F)
    (hR₀ : R.toSubring ≤ V₀.toSubring) (hRinf : R.toSubring ≤ Vinf.toSubring)
    (hzero : f ∈ V₀.nonunits) (hpole : f⁻¹ ∈ Vinf.nonunits)
    (hf : f ≠ 0) (hlevel : f ≠ c) : (f - c)⁻¹ ∉ R.toSubring := by
  intro hreg
  let u : R.toSubring := ⟨(f - c)⁻¹, hreg⟩
  let l : R.toSubring := ⟨c, hc⟩
  let ι₀ := Subring.inclusion hR₀
  let ιinf := Subring.inclusion hRinf
  let φ := (IsLocalRing.residue V₀).comp ι₀
  let ψ := (IsLocalRing.residue Vinf).comp ιinf
  let z : V₀ := ⟨f, V₀.nonunits_subset hzero⟩
  let p : Vinf := ⟨f⁻¹, Vinf.nonunits_subset hpole⟩
  have hz : IsLocalRing.residue V₀ z = 0 :=
    (IsLocalRing.residue_eq_zero_iff z).mpr (V₀.coe_mem_nonunits_iff.mp hzero)
  have hp : IsLocalRing.residue Vinf p = 0 :=
    (IsLocalRing.residue_eq_zero_iff p).mpr (Vinf.coe_mem_nonunits_iff.mp hpole)
  have he₀ : ι₀ u * (z - ι₀ l) = 1 := by
    apply Subtype.ext
    exact inv_mul_cancel₀ (sub_ne_zero.mpr hlevel)
  have heinf : ιinf u * (1 - ιinf l * p) = p := by
    apply Subtype.ext
    change (f - c)⁻¹ * (1 - c * f⁻¹) = f⁻¹
    field_simp
  have he₀' := congrArg (IsLocalRing.residue V₀) he₀
  have heinf' := congrArg (IsLocalRing.residue Vinf) heinf
  simp only [map_mul, map_sub, map_one, hz, zero_sub] at he₀'
  simp only [map_mul, map_sub, map_one, hp, mul_zero, sub_zero, mul_one] at heinf'
  exact local_reciprocal_zero_pole_specializations_impossible φ ψ u l he₀' heinf'

variable (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R F]

/-- For an abstract local ring in its actual function field, a zero
branch and a pole branch exclude regularity of every translated
reciprocal. The level is an original-ring element; its distinctness
from the rational function follows from the pole branch. -/
theorem zero_pole_level_reciprocal_not_isInteger
    (f : F) (c : R) (V₀ Vinf : ValuationSubring F)
    (hR₀ : ∀ a : R, algebraMap R F a ∈ V₀)
    (hRinf : ∀ a : R, algebraMap R F a ∈ Vinf)
    (hzero : f ∈ V₀.nonunits) (hpole : f⁻¹ ∈ Vinf.nonunits) (hf : f ≠ 0) :
    ¬IsLocalization.IsInteger R ((f - algebraMap R F c)⁻¹) := by
  let S := LocalSubring.range (algebraMap R F)
  have hS₀ : S.toSubring ≤ V₀.toSubring := by
    rintro a ⟨b, rfl⟩
    exact hR₀ b
  have hSinf : S.toSubring ≤ Vinf.toSubring := by
    rintro a ⟨b, rfl⟩
    exact hRinf b
  have hlevel : f ≠ algebraMap R F c := by
    intro he
    exact ((Vinf.inv_mem_nonunits_iff.mp hpole).resolve_left hf) (he ▸ hRinf c)
  exact zero_pole_level_reciprocal_not_mem_local_subring S f (algebraMap R F c)
    ⟨c, rfl⟩ V₀ Vinf hS₀ hSinf hzero hpole hf hlevel

end DimensionFourDependence
