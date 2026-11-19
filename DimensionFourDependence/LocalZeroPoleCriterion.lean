import DimensionFourDependence.SeparatingZeroDivisors
import DimensionFourDependence.NormalBranchGeneralLevelClosure

/-! # Constructed local zero branches and denominator-pole criteria give general levels -/

namespace DimensionFourDependence

variable (R : Type*) {B F : Type*}
  [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]
  [CommRing B] [IsLocalRing B] [Field F] [Algebra R F] [IsFractionRing R F]

/-- Nonregularity of a fraction at an actual normal height-one
branch constructs a vanishing germ of its inverse at that same branch. -/
theorem normal_height_one_nonregular_constructs_inverse_zero_germ
    (Q : Ideal R) [Q.IsPrime] (hQ : Q.height = 1) (f : F)
    (hpole : f ∉ fractionPrimeLocalAlgebra R Q) :
    ∃ g : fractionPrimeLocalAlgebra R Q, (g : F) = f⁻¹ ∧
      g ∈ IsLocalRing.maximalIdeal (fractionPrimeLocalAlgebra (F := F) R Q) := by
  obtain ⟨g, hg, hgm⟩ := height_one_reciprocal_pole_is_level R Q hQ f⁻¹ 0
    (by simpa only [sub_zero, inv_inv] using hpole)
  exact ⟨g, by simpa only [sub_zero] using hg, hgm⟩

variable {k : Type*} [Field k] [Algebra k R]

/-- A numerator/denominator specialization constructs both branches
internally. A pole criterion only along actual denominator divisors then
places the original closed point in the closure of every general level. -/
theorem local_zero_and_denominator_poles_construct_general_level_closure
    (φ : R →+* B) (n l : R) (hn : n ≠ 0)
    (hnφ : φ n ∈ IsLocalRing.maximalIdeal B) (hlφ : IsUnit (φ l))
    (hl : l ∈ IsLocalRing.maximalIdeal R) (d : ℕ)
    (hpoles : ∀ Q : PrimeSpectrum R, Q.asIdeal.height = 1 → l ∈ Q.asIdeal →
      algebraMap R F n / (algebraMap R F l) ^ d ∉ fractionPrimeLocalAlgebra R Q.asIdeal) :
    ∃ S : Set k, S.Finite ∧ ∀ c : k, c ∉ S →
      IsLocalRing.closedPoint R ∈ closure (quotientLevelLocus R n (l ^ d) (algebraMap k R c)) := by
  obtain ⟨q₀, qL, hq₀, hqL, hne, hnq₀, hlq₀, hlqL, g₀, hg₀, hgm₀⟩ :=
    local_map_constructs_distinct_zero_and_denominator_divisors (F := F) φ n l hn hnφ hlφ hl d
  let f : F := algebraMap R F n / (algebraMap R F l) ^ d
  have hl0 : l ≠ 0 := by
    intro he
    have hunit : IsUnit (0 : B) := by simpa only [he, map_zero] using hlφ
    exact not_isUnit_zero hunit
  have hnF : algebraMap R F n ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hn
  have hlF : algebraMap R F l ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hl0
  have hf : f ≠ 0 := div_ne_zero hnF (pow_ne_zero d hlF)
  have hquot : algebraMap R F (l ^ d) * f = algebraMap R F n := by
    dsimp only [f]
    rw [map_pow]
    exact mul_div_cancel₀ _ (pow_ne_zero d hlF)
  obtain ⟨gL, hgL, hgmL⟩ := normal_height_one_nonregular_constructs_inverse_zero_germ
    R qL.asIdeal hqL f (hpoles qL hqL hlqL)
  exact normal_branch_zero_pole_general_quotient_level_closure (k := k) R f n (l ^ d)
    (pow_ne_zero d hl0) hquot q₀.asIdeal qL.asIdeal hq₀ hqL
    ⟨g₀, hg₀, hgm₀⟩ ⟨gL, hgL, hgmL⟩ hf

end DimensionFourDependence
