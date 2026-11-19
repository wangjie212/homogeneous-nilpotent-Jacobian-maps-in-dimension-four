import DimensionFourDependence.SegreFiniteProjectiveRulingPoint

/-! # The geometric boundary parameter is the original rational ruling parameter -/

namespace DimensionFourDependence

open MvPolynomial
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]

/-- The specified original ruling parameter remains transcendental in
every compatible extension of the constants of an actual geometric component. -/
theorem original_segre_geometric_ruling_parameter_transcendental
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (E : Type u) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (Q : Ideal (MvPolynomial (Fin 4) E)) [Q.IsPrime]
    (hQ : Q ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (j : Fin 3) (hj : j ≠ 0)
    (κ : Type u) [Field κ] [Algebra E κ] [Algebra K κ] [IsScalarTower K E κ] :
    Transcendental K (algebraMap E κ (genericOutputValue H E j.castSucc / genericOutputValue H E 0)) := by
  obtain ⟨hY, c, q, k, hc, hq, hk, _he, _hce, _hqe⟩ :=
    exists_original_segre_weighted_fiber_invariants H hd hH hN hrank hind hSegre
  obtain ⟨R⟩ := segre_original_fiber_invariants_geometric_realization
    H hind hSegre hY c q k hc hq hk hrank E Q hQ
  let g : coefficientField (K := K) (segreOriginalOutputTriple H) →ₐ[K] E :=
    { toRingHom := R.coefficientMap, commutes' := R.scalar_image }
  let f := (IsScalarTower.toAlgHom K E κ).comp g
  have ht : f (segreCoefficientRulingParameter (segreOriginalOutputTriple H) j) =
      algebraMap E κ (genericOutputValue H E j.castSucc / genericOutputValue H E 0) := by
    change algebraMap E κ (R.coefficientMap (coefficientCoordinate (K := K) (segreOriginalOutputTriple H) j /
      coefficientCoordinate (K := K) (segreOriginalOutputTriple H) 0)) = _
    rw [map_div₀, R.coordinate_image, R.coordinate_image]
    rfl
  rw [← ht]
  intro he
  exact segre_coefficient_ruling_parameter_transcendental (segreOriginalOutputTriple H) hY j hj
    ((isAlgebraic_algHom_iff f f.injective).mp he)

/-- The original parameter field in the normalized coordinate field of
any actual projective prime is isomorphic to the rational function field,
with no enlargement of its constant field. -/
theorem segreProjectiveRulingParameterField_rational
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (E : Type u) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (Q : Ideal (MvPolynomial (Fin 4) E)) [Q.IsPrime]
    (hQ : Q ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (j : Fin 3) (hj : j ≠ 0)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E)) (a : Fin 4) :
    Nonempty (RatFunc K ≃ₐ[K] segreProjectiveRulingParameterField K (genericOutputValue H E) j p a) := by
  let κ := projectivePrimeRatioField p (some a)
  let t := algebraMap E κ (genericOutputValue H E j.castSucc / genericOutputValue H E 0)
  have ht : Transcendental K t := original_segre_geometric_ruling_parameter_transcendental
    H hd hH hN hrank hind hSegre E Q hQ j hj κ
  let f := transcendentalParameterFieldHom t ht
  have hf : f.fieldRange = segreProjectiveRulingParameterField K (genericOutputValue H E) j p a := by
    rw [rational_function_algHom_fieldRange_eq_adjoin_parameter]
    rw [show f RatFunc.X = t from transcendentalParameterFieldHom_X t ht]
    rfl
  exact ⟨f.equivFieldRange.trans (IntermediateField.equivOfEq hf)⟩

end DimensionFourDependence
