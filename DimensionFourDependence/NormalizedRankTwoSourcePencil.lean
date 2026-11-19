import DimensionFourDependence.HomogeneousRankTwoPolynomialPencil
import DimensionFourDependence.BinaryPencilPointNormalization
import DimensionFourDependence.HomogeneousBinaryDehomogenization
import DimensionFourDependence.HomogenizedParameterSourceJets

/-! # The actual rank-two map constructs a source pencil normalized at its original point -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 3500000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- At an actual original point with nonzero output, the homogeneous
rank-two map constructs a primitive polynomial pencil factorization
whose source numerator and denominator take the exact values zero and
one. The common scalar is nonzero at that point. All generators,
homogeneous degrees and parameter polynomials are derived. -/
theorem homogeneous_rank_two_map_constructs_point_normalized_primitive_source_pencil
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 2) (z : Fin 4 → K) (hHz : aeval z (H 1) ≠ 0) :
    ∃ (p q g : R₀) (D N c : ℕ) (v : Fin 4 → Polynomial K),
      0 < D ∧ 0 < N ∧ g ≠ 0 ∧ p.IsHomogeneous D ∧ q.IsHomogeneous D ∧
      g.IsHomogeneous c ∧ c + D * N = d ∧ IsRelPrime p q ∧
      aeval z p = 0 ∧ aeval z q = 1 ∧ aeval z g ≠ 0 ∧
      (∀ i, (v i).natDegree ≤ N) ∧
      IsPrimitiveVec (fun i => homogeneousParameterPolynomialValue (v i) N p q) ∧
      ∀ i, H i = g * homogeneousParameterPolynomialValue (v i) N p q := by
  classical
  obtain ⟨p, q, g, D, N, c, v, hD, hNpos, _hp, _hq, hg, hpH, hqH, hgH,
    hdegree, hrel, hN, _htop, _hvprim, hprim, _hvH, hfactor⟩ :=
    homogeneous_rank_two_map_constructs_primitive_polynomial_binary_pencil_factorization H hd hH hrank
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
  have hbinary (i : Fin 4) :
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

end DimensionFourDependence
