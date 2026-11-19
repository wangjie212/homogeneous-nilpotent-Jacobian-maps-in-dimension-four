import DimensionFourDependence.GeneralHomogeneousRankTwoPencil
import DimensionFourDependence.TernaryNilpotentPencilMinor
import DimensionFourDependence.LinearConjugacyRank
import DimensionFourDependence.BinaryPencilPointNormalization
import DimensionFourDependence.HomogeneousBinaryDehomogenization
import DimensionFourDependence.HomogenizedParameterSourceJets

/-! # The actual rank-two map constructs a source pencil normalized at its original point -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 3500000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 3) K

/-- At an actual original point with nonzero output, the homogeneous
rank-two map constructs a primitive polynomial pencil factorization
whose source numerator and denominator take the exact values zero and
one. The common scalar is nonzero at that point. All generators,
homogeneous degrees and parameter polynomials are derived. -/
theorem ternary_homogeneous_rank_two_map_constructs_point_normalized_primitive_source_pencil
    (H : Fin 3 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 2) (z : Fin 3 → K) (hHz : aeval z (H 1) ≠ 0) :
    ∃ (p q g : R₀) (D N c : ℕ) (v : Fin 3 → Polynomial K),
      0 < D ∧ 0 < N ∧ g ≠ 0 ∧ p.IsHomogeneous D ∧ q.IsHomogeneous D ∧
      g.IsHomogeneous c ∧ c + D * N = d ∧ IsRelPrime p q ∧
      aeval z p = 0 ∧ aeval z q = 1 ∧ aeval z g ≠ 0 ∧
      (∀ i, (v i).natDegree ≤ N) ∧
      IsPrimitiveVec (fun i => homogeneousParameterPolynomialValue (v i) N p q) ∧
      ∀ i, H i = g * homogeneousParameterPolynomialValue (v i) N p q := by
  classical
  obtain ⟨p, q, g, D, N, c, v, hD, hNpos, _hp, _hq, hg, hpH, hqH, hgH,
    hdegree, hrel, hN, _htop, _hvprim, hprim, _hvH, hfactor⟩ :=
    general_homogeneous_rank_two_map_constructs_primitive_polynomial_binary_pencil_factorization H hd hH hrank
  have hpoint : (![aeval z p, aeval z q] : Fin 2 → K) ≠ 0 := by
    intro hz
    have hpz : aeval z p = 0 := congrFun hz 0
    have hqz : aeval z q = 0 := congrFun hz 1
    have hzero : aeval (fun _ : Fin 2 => (0 : K)) ((v 1).homogenize N) = 0 := by
      have he := homogeneous_aeval_scale ((v 1).homogenize N)
        (Polynomial.isHomogeneous_homogenize (v 1)) (0 : Fin 2 → K) (0 : K)
      simpa only [Pi.zero_apply, zero_mul, zero_pow hNpos.ne'] using he
    have hpair : (fun i => aeval z (![p, q] i)) = (fun _ : Fin 2 => (0 : K)) := by
      funext i
      fin_cases i <;> assumption
    have he := congrArg (aeval z) (hfactor 1)
    rw [map_mul, comp_aeval_apply, hpair, hzero, mul_zero] at he
    exact hHz he
  obtain ⟨T, S, p', q', _hTS, _hST, hp'H, hq'H, hrel', hp'z, hq'z, _hrestore, hpreserve⟩ :=
    nonbase_source_point_constructs_normalized_homogeneous_binary_pencil p q hpH hqH hrel z hpoint
  have hbinary (i : Fin 3) :
      (linearPolynomialPullback T ((v i).homogenize N)).IsHomogeneous N :=
    linearPolynomialPullback_homogeneous T _ (Polynomial.isHomogeneous_homogenize (v i))
  choose w hwN hwF using fun i => homogeneous_binary_form_constructs_bounded_univariate_parameter
    (linearPolynomialPullback T ((v i).homogenize N)) (hbinary i)
  have hvalues (i) : homogeneousParameterPolynomialValue (w i) N p' q' =
      homogeneousParameterPolynomialValue (v i) N p q := by
    rw [homogeneousParameterPolynomialValue, hwF, hpreserve]
    rfl
  have hfactor' (i) : H i = g * homogeneousParameterPolynomialValue (w i) N p' q' := by
    rw [hvalues]
    exact hfactor i
  have hprim' : IsPrimitiveVec (fun i => homogeneousParameterPolynomialValue (w i) N p' q') := by
    simpa only [hvalues] using hprim
  have hgz : aeval z g ≠ 0 := by
    intro hz
    have he := congrArg (aeval z) (hfactor' 1)
    rw [map_mul, hz, zero_mul] at he
    exact hHz he
  exact ⟨p', q', g, D, N, c, w, hD, hNpos, hg, hp'H, hq'H, hgH, hdegree,
    hrel', hp'z, hq'z, hgz, hwN, hprim', hfactor'⟩

/-- A hypothetical independent original ternary nilpotent rank-two map
constructs its normalized source frame, primitive polynomial pencil,
actual parameter jets, inactive square divisor and active tangent
minor, all over the original closed characteristic-zero field. -/
theorem original_independent_ternary_rank_two_nilpotent_map_constructs_normalized_pencil_and_active_minor
    (H : Fin 3 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 2) (hind : ¬ComponentsDependent H) :
    ∃ T S : Matrix (Fin 3) (Fin 3) K, T * S = 1 ∧ S * T = 1 ∧
      let G := linearPolynomialConjugate T S H
      IsHomogMap G d ∧ IsNilpotent (jac G) ∧ ¬ComponentsDependent G ∧ polyRank (jac G) = 2 ∧
      (∀ i, aeval (Pi.single (0 : Fin 3) (1 : K)) (pderiv 0 (G i)) = if i = 1 then 1 else 0) ∧
      (∀ i, aeval (Pi.single (0 : Fin 3) (1 : K)) (pderiv 1 (G i)) = if i = 2 then 1 else 0) ∧
      ∃ (p q g : R₀) (D N c : ℕ) (v : Fin 3 → Polynomial K),
        0 < D ∧ 0 < N ∧ g ≠ 0 ∧ p.IsHomogeneous D ∧ q.IsHomogeneous D ∧ g.IsHomogeneous c ∧
        c + D * N = d ∧ IsRelPrime p q ∧
        aeval (Pi.single (0 : Fin 3) (1 : K)) p = 0 ∧ aeval (Pi.single (0 : Fin 3) (1 : K)) q = 1 ∧
        aeval (Pi.single (0 : Fin 3) (1 : K)) g ≠ 0 ∧
        aeval (Pi.single (0 : Fin 3) (1 : K)) (pderiv 1 p) ≠ 0 ∧
        (∀ i, (v i).natDegree ≤ N) ∧ IsPrimitiveVec (fun i => homogeneousParameterPolynomialValue (v i) N p q) ∧
        (∀ i, G i = g * homogeneousParameterPolynomialValue (v i) N p q) ∧
        g * p ^ 2 ∣ G 0 ∧ p ∣ sourceJacobianMinor (G 1) p 1 2 := by
  obtain ⟨T, S, hTS, hST, hGhom, hGnil, hGind, hcol0, hcol1⟩ :=
    original_independent_homogeneous_ternary_nilpotent_map_constructs_normalized_point_frame H hd hH hN hind
  let G := linearPolynomialConjugate T S H
  have hrG : polyRank (jac G) = 2 := (linearPolynomialConjugate_polyRank T S hTS hST H).trans hrank
  obtain ⟨hvalue, hnonzero⟩ := ternary_normalized_first_jacobian_column_output_support_and_nonzero G hd hGhom hcol0
  obtain ⟨p, q, g, D, N, c, v, hD, hNpos, hg, hpH, hqH, hgH, hdegree, hrel,
    hp0, hq1, hgz, hVdeg, hprim, hfactor⟩ :=
    ternary_homogeneous_rank_two_map_constructs_point_normalized_primitive_source_pencil
      G hd hGhom hrG (Pi.single (0 : Fin 3) (1 : K)) hnonzero
  obtain ⟨hpder, hv0, _hv01, hdiv0⟩ :=
    ternary_normalized_parameter_output_jets_construct_nonzero_pencil_derivative_and_square_divisor
      G p q g (Pi.single (0 : Fin 3) (1 : K)) hp0 hq1 hgz v hVdeg hfactor hvalue hcol1
  have hminor := ternary_normalized_nilpotent_source_pencil_forces_active_minor_divisibility
    G p q g hg hrel (Pi.single (0 : Fin 3) (1 : K)) hp0 hq1 v hVdeg hfactor
    (hv0 2 (by decide)) (by simpa using hcol1 2) hdiv0 hGnil
  exact ⟨T, S, hTS, hST, hGhom, hGnil, hGind, hrG, hcol0, hcol1,
    p, q, g, D, N, c, v, hD, hNpos, hg, hpH, hqH, hgH, hdegree, hrel,
    hp0, hq1, hgz, hpder, hVdeg, hprim, hfactor, hdiv0, hminor⟩

end DimensionFourDependence
