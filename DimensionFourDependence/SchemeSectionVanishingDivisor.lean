import DimensionFourDependence.PrincipalVanishingDivisor
import DimensionFourDependence.NormalDivisorStalkDvr
import Mathlib.AlgebraicGeometry.FunctionField

/-! # A nonzero regular coefficient has a prime divisor through each zero -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite IsLocalRing

universe u
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 115000

/-- A point at which a nonzero regular section vanishes lies in the
closure of an actual codimension-one point of its zero locus. -/
theorem scheme_regular_section_zero_has_prime_divisor
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) (s : Γ(X, U)) (hs : s ≠ 0) (p : X) (hp : p ∈ U)
    (hz : X.presheaf.germ U p hp s ∈ maximalIdeal (X.presheaf.stalk p)) :
    ∃ (q : X) (hq : q ∈ U), q ⤳ p ∧ Order.coheight q = 1 ∧
      X.presheaf.germ U q hq s ∈ maximalIdeal (X.presheaf.stalk q) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hp U.isOpen
  let R := Γ(X, V)
  let : Nonempty V := ⟨⟨p, hpV⟩⟩
  let : IsDomain R := Function.Injective.isDomain (X.germToFunctionField V).hom
    (X.germToFunctionField_injective V)
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian (X := X) ⟨V, hV⟩
  let j : V ⟶ U := homOfLE hVU
  let t : R := X.presheaf.map j.op s
  have ht : t ≠ 0 := by
    intro ht₀
    apply hs
    exact map_injective_of_isIntegral X j
      (ht₀.trans ((X.presheaf.map j.op).hom.map_zero).symm)
  let P := hV.primeIdealOf ⟨p, hpV⟩
  have hP : t ∈ P.asIdeal := by
    change t ∈ (hV.primeIdealOf ⟨p, hpV⟩).asIdeal
    rw [hV.primeIdealOf_eq_map_closedPoint]
    change X.presheaf.germ V p hpV t ∈ maximalIdeal (X.presheaf.stalk p)
    exact (X.presheaf.germ_res_apply (homOfLE hVU) p hpV s).symm ▸ hz
  obtain ⟨r, hr, htr, hrP⟩ := nonzero_function_prime_contains_vanishing_divisor t ht P.asIdeal hP
  let q : V := hV.isoSpec.inv r
  have hq : hV.primeIdealOf q = r := by
    change hV.isoSpec.hom (hV.isoSpec.inv r) = r
    exact Scheme.inv_hom_apply hV.isoSpec r
  have hqP : (q : X) ⤳ p := by
    have hsp : r ⤳ P := (PrimeSpectrum.le_iff_specializes _ _).mp hrP
    have he := hsp.map hV.fromSpec.continuous
    simpa only [← hq, P, hV.fromSpec_primeIdealOf] using he
  have hq₁ : Order.coheight (q : X) = 1 := by
    let : Algebra R (X.presheaf.stalk (q : X)) := X.presheaf.algebra_section_stalk q
    let : IsLocalization.AtPrime (X.presheaf.stalk (q : X)) (hV.primeIdealOf q).asIdeal :=
      hV.isLocalization_stalk q
    have he := IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf q).asIdeal (X.presheaf.stalk (q : X))
    rw [ringKrullDim_stalk_eq_coheight, hq, hr] at he
    exact_mod_cast he
  have hqU := hVU q.property
  refine ⟨q.val, hqU, hqP, hq₁, ?_⟩
  have hqr : t ∈ (hV.primeIdealOf q).asIdeal := hq.symm ▸ htr
  rw [hV.primeIdealOf_eq_map_closedPoint] at hqr
  change X.presheaf.germ V q.val q.property t ∈ maximalIdeal (X.presheaf.stalk _) at hqr
  have he : X.presheaf.germ V q.val q.property t = X.presheaf.germ U q.val hqU s :=
    X.presheaf.germ_res_apply j q.val q.property s
  rwa [he] at hqr

end DimensionFourDependence
