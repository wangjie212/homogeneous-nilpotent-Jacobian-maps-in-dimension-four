import DimensionFourDependence.SeparatingZeroDivisors
import DimensionFourDependence.NormalBranchGeneralLevelClosure
import DimensionFourDependence.NormalGraphResidueKernel

/-! # Separated zero and denominator divisors make the pencil parameter free at a base point -/

namespace DimensionFourDependence

variable {k R B F : Type*} [Field k] [Infinite k]
  [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [IsIntegrallyClosed R]
  [Algebra k R] [CommRing B] [IsLocalRing B]
  [Field F] [Algebra R F] [IsFractionRing R F]

include k in
/-- A separating specialization and absence of common height-one
components construct the zero and pole valuations needed for a free
graph residue parameter at the original base point. -/
theorem separated_local_pencil_graph_kernel_le_residue_polynomial_kernel
    (φ : R →+* B) (a b : R) (ha : a ≠ 0)
    (haφ : φ a ∈ IsLocalRing.maximalIdeal B) (hbφ : IsUnit (φ b))
    (hb : b ∈ IsLocalRing.maximalIdeal R)
    (hsep : ∀ Q : PrimeSpectrum R, Q.asIdeal.height = 1 → b ∈ Q.asIdeal → a ∉ Q.asIdeal) :
    RingHom.ker (Polynomial.aeval (algebraMap R F a / algebraMap R F b)).toRingHom ≤
      RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue R)) := by
  obtain ⟨Q₀, Qinf, hQ₀, hQinf, _hne, haQ₀, hbQ₀, hbQinf, g₀, hg₀, hgm₀⟩ :=
    local_map_constructs_distinct_zero_and_denominator_divisors (F := F) φ a b ha haφ hbφ hb 1
  have haQinf := hsep Qinf hQinf hbQinf
  obtain ⟨ginf, hginf, hgminf⟩ :=
    quotient_constructs_vanishing_prime_local_germ (F := F) Qinf.asIdeal b a hbQinf haQinf 1
  let f := algebraMap R F a / algebraMap R F b
  let V₀ := normalHeightOneValuationSubring (F := F) R Q₀.asIdeal hQ₀
  let Vinf := normalHeightOneValuationSubring (F := F) R Qinf.asIdeal hQinf
  have hg₀f : (g₀ : F) = f := by simpa only [pow_one] using hg₀
  have hginvf : (ginf : F) = f⁻¹ := by
    simpa only [f, inv_div, pow_one] using hginf
  have hz : f ∈ V₀.nonunits := hg₀f ▸
    normal_branch_vanishing_mem_valuation_nonunits R Q₀.asIdeal hQ₀ g₀ hgm₀
  have hp : f⁻¹ ∈ Vinf.nonunits := hginvf ▸
    normal_branch_vanishing_mem_valuation_nonunits R Qinf.asIdeal hQinf ginf hgminf
  have hb0 : b ≠ 0 := fun he => hbQ₀ (he ▸ Q₀.asIdeal.zero_mem)
  have hf : f ≠ 0 := div_ne_zero
    ((map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr ha)
    ((map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hb0)
  exact zero_pole_graph_kernel_le_residue_polynomial_kernel (k := k) f V₀ Vinf
    (fun r => (fractionPrimeLocalAlgebra (F := F) R Q₀.asIdeal).algebraMap_mem r)
    (fun r => (fractionPrimeLocalAlgebra (F := F) R Qinf.asIdeal).algebraMap_mem r) hz hp hf

end DimensionFourDependence
