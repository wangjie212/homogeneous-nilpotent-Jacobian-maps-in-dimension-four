import DimensionFourDependence.GeneralRationalLevelDivisors

/-! # Zero/pole intersection lies on the closure of a general quotient level

This is the local zero/pole argument in the precise domain used by a
chosen numerator and denominator. It constructs the finite exceptional
set, a height-one point of every remaining level in the denominator's
principal open, and specialization to the original closed point.
The codimension-one regularity consequence of normality and denominator
generality are proved in the preceding modules. Normality and
Noetherianity are hypotheses on the local domain.
-/

namespace DimensionFourDependence

variable (R : Type*) [CommRing R]

/-- The level hypersurface in the domain of the specified quotient. -/
def quotientLevelLocus (a b c : R) : Set (PrimeSpectrum R) :=
  {p | b ∉ p.asIdeal ∧ a - c * b ∈ p.asIdeal}

/-- The quotient level is exactly the original hypersurface
intersected with the denominator's principal open. -/
theorem quotientLevelLocus_eq_basicOpen_inter_zeroLocus (a b c : R) :
    quotientLevelLocus R a b c = (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum R)) ∩
      PrimeSpectrum.zeroLocus {a - c * b} := by
  ext p
  change (b ∉ p.asIdeal ∧ a - c * b ∈ p.asIdeal) ↔
    (b ∉ p.asIdeal ∧ ({a - c * b} : Set R) ⊆ (p.asIdeal : Set R))
  rw [Set.singleton_subset_iff]
  rfl

variable {k F : Type*} [Field k] [IsDomain R] [Algebra k R] [Field F]
  [Algebra R F] [IsFractionRing R F] [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- If every translated reciprocal is nonregular, then for all but
finitely many original constants the specified quotient level has a
height-one point in its actual denominator open. -/
theorem nonregular_reciprocals_construct_general_quotient_level_points
    (f : F) (a b : R) (hb : b ≠ 0)
    (hquot : algebraMap R F b * f = algebraMap R F a)
    (hreg : ∀ c : k, ¬IsLocalization.IsInteger R
      ((f - algebraMap R F (algebraMap k R c))⁻¹)) :
    ∃ S : Set k, S.Finite ∧ ∀ c ∉ S, ∃ p : PrimeSpectrum R,
      p.asIdeal.height = 1 ∧ p ∈ quotientLevelLocus R a b (algebraMap k R c) := by
  obtain ⟨S, hS, hgood⟩ := finite_exceptional_levels_for_denominator (k := k) f b hb
  refine ⟨S, hS, ?_⟩
  intro c hc
  obtain ⟨p, hh, hp⟩ := normal_nonregular_reciprocal_constructs_height_one_level_point
    R f (algebraMap k R c) (hreg c)
  exact ⟨p, hh, hgood c hc p hh hp,
    rationalLevelLocus_original_quotient_equation f a b (algebraMap k R c) hquot p hp⟩

variable [IsLocalRing R]

/-- The normal local zero/pole intersection lies in the closure of
the general level of the original quotient on its prescribed domain.
The exceptional constants form an actually constructed finite set. -/
theorem zero_pole_general_quotient_level_closed_point_closure
    (f : F) (a b : R) (hb : b ≠ 0)
    (hquot : algebraMap R F b * f = algebraMap R F a)
    (V₀ Vinf : ValuationSubring F)
    (hR₀ : ∀ r : R, algebraMap R F r ∈ V₀)
    (hRinf : ∀ r : R, algebraMap R F r ∈ Vinf)
    (hzero : f ∈ V₀.nonunits) (hpole : f⁻¹ ∈ Vinf.nonunits) (hf : f ≠ 0) :
    ∃ S : Set k, S.Finite ∧ ∀ c ∉ S,
      (⟨IsLocalRing.maximalIdeal R, inferInstance⟩ : PrimeSpectrum R) ∈
        closure (quotientLevelLocus R a b (algebraMap k R c)) := by
  obtain ⟨S, hS, hpoint⟩ := nonregular_reciprocals_construct_general_quotient_level_points
    R f a b hb hquot (fun c => zero_pole_level_reciprocal_not_isInteger
      R f (algebraMap k R c) V₀ Vinf hR₀ hRinf hzero hpole hf)
  refine ⟨S, hS, ?_⟩
  intro c hc
  obtain ⟨p, hh, hp⟩ := hpoint c hc
  have hle : p ≤ (⟨IsLocalRing.maximalIdeal R, inferInstance⟩ : PrimeSpectrum R) :=
    IsLocalRing.le_maximalIdeal p.isPrime.ne_top
  exact closure_mono (Set.singleton_subset_iff.mpr hp)
    ((PrimeSpectrum.le_iff_mem_closure _ _).mp hle)

end DimensionFourDependence
