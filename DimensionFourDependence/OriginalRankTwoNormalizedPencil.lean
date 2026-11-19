import DimensionFourDependence.NormalizedRankTwoSourcePencil
import DimensionFourDependence.NormalizedJacobianParameterJets
import DimensionFourDependence.LinearConjugacyRank
import DimensionFourDependence.NormalizedPencilActiveMinor

/-! # A hypothetical original rank-two counterexample constructs its normalized source pencil -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 3500000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- The original homogeneous nilpotent rank-two map and hypothetical
component independence construct the entire normalized point, inverse
coordinates, primitive polynomial pencil, exact degrees and double
inactive divisors. No Jordan frame, point, source pencil, parameter
polynomials, divisors or first-order conditions are supplied. -/
theorem original_independent_rank_two_nilpotent_map_constructs_normalized_primitive_pencil_and_double_divisors
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 2)
    (hind : ¬ComponentsDependent H) :
    ∃ T S : Matrix (Fin 4) (Fin 4) K,
      T * S = 1 ∧ S * T = 1 ∧
      let G := linearPolynomialConjugate T S H
      IsHomogMap G d ∧ IsNilpotent (jac G) ∧ ¬ComponentsDependent G ∧ polyRank (jac G) = 2 ∧
      (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K)) (pderiv 0 (G i)) = if i = 1 then 1 else 0) ∧
      (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K)) (pderiv 1 (G i)) = if i = 2 then 1 else 0) ∧
      ∃ (p q g : R₀) (D N c : ℕ) (v : Fin 4 → Polynomial K),
        0 < D ∧ 0 < N ∧ g ≠ 0 ∧ p.IsHomogeneous D ∧ q.IsHomogeneous D ∧
        g.IsHomogeneous c ∧ c + D * N = d ∧ IsRelPrime p q ∧
        aeval (Pi.single (0 : Fin 4) (1 : K)) p = 0 ∧
        aeval (Pi.single (0 : Fin 4) (1 : K)) q = 1 ∧
        aeval (Pi.single (0 : Fin 4) (1 : K)) g ≠ 0 ∧
        aeval (Pi.single (0 : Fin 4) (1 : K)) (pderiv 1 p) ≠ 0 ∧
        (∀ i, (v i).natDegree ≤ N) ∧
        IsPrimitiveVec (fun i => homogeneousParameterPolynomialValue (v i) N p q) ∧
        (∀ i, G i = g * homogeneousParameterPolynomialValue (v i) N p q) ∧
        (∀ i, i ≠ 1 → (v i).coeff 0 = 0) ∧
        (v 0).coeff 1 = 0 ∧ (v 3).coeff 1 = 0 ∧
        g * p ^ 2 ∣ G 0 ∧ g * p ^ 2 ∣ G 3 ∧
        p ∣ sourceJacobianMinor (G 1) p 1 2 := by
  obtain ⟨T, S, hTS, hST, hGhom, hGnil, hGind, hcol0, hcol1⟩ :=
    original_independent_homogeneous_nilpotent_map_constructs_normalized_point_frame H hd hH hN hind
  let G := linearPolynomialConjugate T S H
  have hrG : polyRank (jac G) = 2 := (linearPolynomialConjugate_polyRank T S hTS hST H).trans hrank
  obtain ⟨hvalue, hnonzero⟩ := normalized_first_jacobian_column_output_support_and_nonzero
    G hd hGhom hcol0
  obtain ⟨p, q, g, D, N, c, v, hD, hNpos, hg, hpH, hqH, hgH, hdegree, hrel,
    hp0, hq1, hgz, hVdeg, hprim, hfactor⟩ :=
    homogeneous_rank_two_map_constructs_point_normalized_primitive_source_pencil
      G hd hGhom hrG (Pi.single (0 : Fin 4) (1 : K)) hnonzero
  obtain ⟨hpder, hv0, hv01, hv31, hdiv0, hdiv3⟩ :=
    normalized_parameter_output_jets_construct_nonzero_pencil_derivative_and_square_divisors
      G p q g (Pi.single (0 : Fin 4) (1 : K)) hp0 hq1 hgz v hVdeg hfactor hvalue hcol1
  have hminor := normalized_nilpotent_source_pencil_forces_active_minor_divisibility
    G p q g hg hrel (Pi.single (0 : Fin 4) (1 : K)) hp0 hq1 v hVdeg hfactor
    (hv0 2 (by decide)) (by simpa using hcol1 2) hdiv0 hdiv3 hGnil
  exact ⟨T, S, hTS, hST, hGhom, hGnil, hGind, hrG, hcol0, hcol1,
    p, q, g, D, N, c, v, hD, hNpos, hg, hpH, hqH, hgH, hdegree, hrel,
    hp0, hq1, hgz, hpder, hVdeg, hprim, hfactor, hv0, hv01, hv31, hdiv0, hdiv3, hminor⟩

end DimensionFourDependence
