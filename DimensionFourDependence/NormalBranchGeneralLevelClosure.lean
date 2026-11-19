import DimensionFourDependence.ZeroPoleGeneralLevelClosure

/-! # The general-level closure theorem from actual branch local rings

Height-one branches in the original normal Noetherian local domain
construct their own valuation subrings in its specified function field.
Thus the zero/pole closure theorem accepts actual vanishing branch germs,
without any separately supplied valuation extensions or residue maps.
-/

namespace DimensionFourDependence

variable (R : Type*) {F : Type*} [CommRing R] [IsDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F] [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- The valuation subring belonging to the actual height-one
localization of a normal Noetherian domain. -/
noncomputable def normalHeightOneValuationSubring
    (P : Ideal R) [P.IsPrime] (hh : P.height = 1) : ValuationSubring F where
  toSubring := (fractionPrimeLocalAlgebra (F := F) R P).toSubring
  mem_or_inv_mem' := by
    intro x
    let T := fractionPrimeLocalAlgebra (F := F) R P
    let : IsDiscreteValuationRing T := normal_height_one_prime_local_algebra_isDVR R P hh
    rcases ValuationRing.isInteger_or_isInteger T x with ⟨z, hz⟩ | ⟨z, hz⟩
    · exact Or.inl (hz ▸ z.property)
    · exact Or.inr (hz ▸ z.property)

/-- A vanishing germ in the actual branch localization is a
nonunit in its constructed original-field valuation subring. -/
theorem normal_branch_vanishing_mem_valuation_nonunits
    (P : Ideal R) [P.IsPrime] (hh : P.height = 1)
    (z : fractionPrimeLocalAlgebra (F := F) R P)
    (hz : z ∈ IsLocalRing.maximalIdeal (fractionPrimeLocalAlgebra (F := F) R P)) :
    (z : F) ∈ (normalHeightOneValuationSubring R P hh).nonunits := by
  let V := normalHeightOneValuationSubring (F := F) R P hh
  apply (V.coe_mem_nonunits_iff (a := ⟨(z : F), z.property⟩)).mpr
  rw [IsLocalRing.mem_maximalIdeal] at hz ⊢
  exact hz

variable {k : Type*} [Field k] [Algebra k R] [IsLocalRing R]

/-- At a normal local intersection of actual height-one zero and
pole branches, the original closed point lies in the closure of the
general level in the chosen quotient's denominator open. -/
theorem normal_branch_zero_pole_general_quotient_level_closure
    (f : F) (a b : R) (hb : b ≠ 0)
    (hquot : algebraMap R F b * f = algebraMap R F a)
    (P₀ Pinf : Ideal R) [P₀.IsPrime] [Pinf.IsPrime]
    (hh₀ : P₀.height = 1) (hhinf : Pinf.height = 1)
    (hzero : ∃ z : fractionPrimeLocalAlgebra (F := F) R P₀,
      (z : F) = f ∧ z ∈ IsLocalRing.maximalIdeal (fractionPrimeLocalAlgebra (F := F) R P₀))
    (hpole : ∃ z : fractionPrimeLocalAlgebra (F := F) R Pinf,
      (z : F) = f⁻¹ ∧ z ∈ IsLocalRing.maximalIdeal (fractionPrimeLocalAlgebra (F := F) R Pinf))
    (hf : f ≠ 0) :
    ∃ S : Set k, S.Finite ∧ ∀ c ∉ S,
      (⟨IsLocalRing.maximalIdeal R, inferInstance⟩ : PrimeSpectrum R) ∈
        closure (quotientLevelLocus R a b (algebraMap k R c)) := by
  let V₀ := normalHeightOneValuationSubring (F := F) R P₀ hh₀
  let Vinf := normalHeightOneValuationSubring (F := F) R Pinf hhinf
  have hR₀ (r : R) : algebraMap R F r ∈ V₀ :=
    (fractionPrimeLocalAlgebra (F := F) R P₀).algebraMap_mem r
  have hRinf (r : R) : algebraMap R F r ∈ Vinf :=
    (fractionPrimeLocalAlgebra (F := F) R Pinf).algebraMap_mem r
  obtain ⟨z₀, hz₀, hvan₀⟩ := hzero
  obtain ⟨zinf, hzinf, hvaninf⟩ := hpole
  have hzeroV : f ∈ V₀.nonunits := hz₀ ▸
    normal_branch_vanishing_mem_valuation_nonunits R P₀ hh₀ z₀ hvan₀
  have hpoleV : f⁻¹ ∈ Vinf.nonunits := hzinf ▸
    normal_branch_vanishing_mem_valuation_nonunits R Pinf hhinf zinf hvaninf
  exact zero_pole_general_quotient_level_closed_point_closure
    R f a b hb hquot V₀ Vinf hR₀ hRinf hzeroV hpoleV hf

end DimensionFourDependence
