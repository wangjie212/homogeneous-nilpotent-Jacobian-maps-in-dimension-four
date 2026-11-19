import DimensionFourDependence.HomogeneousRankTwoProjectiveParameter
import DimensionFourDependence.PolynomialSourcePencilFactorization

/-! # The actual homogeneous rank-two map factors polynomially through two forms -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 3000000

variable {K : Type u} [Field K] {n : ℕ}

/-- A polynomial map with one common scalar and constant direction
has Jacobian rank at most one, by the actual outer-product matrix. -/
theorem polynomial_scalar_constant_vector_jacobian_rank_at_most_one
    (g : MvPolynomial (Fin n) K) (c : Fin n → K) :
    polyRank (jac (fun i => g * C (c i))) ≤ 1 := by
  have hJ : (jac (fun i => g * C (c i))).map
      (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))) =
      Matrix.vecMulVec
        (fun i => algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (C (c i)))
        (fun j => algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (pderiv j g)) := by
    funext i j
    change algebraMap _ _ (pderiv j (g * C (c i))) = _
    rw [pderiv_mul, pderiv_C, mul_zero, add_zero, map_mul]
    exact mul_comm _ _
  unfold polyRank
  rw [hJ]
  exact Matrix.rank_vecMulVec_le _ _

variable [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- The original positive homogeneous rank-two four-variable map
constructs two reduced positive homogeneous forms of the same degree,
a nonzero homogeneous common factor, and homogeneous binary parameter
forms of a common positive degree. Their evaluation is primitive and
their product with the common factor is the original map. This is the
rank-two structure theorem, with every datum derived from the actual
map; nilpotence, coordinates and a parametrization are not supplied. -/
theorem homogeneous_rank_two_map_constructs_primitive_polynomial_binary_pencil_factorization
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 2) :
    ∃ (p q g : R₀) (D N c : ℕ) (v : Fin 4 → Polynomial K),
      0 < D ∧ 0 < N ∧ p ≠ 0 ∧ q ≠ 0 ∧ g ≠ 0 ∧
      p.IsHomogeneous D ∧ q.IsHomogeneous D ∧ g.IsHomogeneous c ∧
      c + D * N = d ∧ IsRelPrime p q ∧
      (∀ i, (v i).natDegree ≤ N) ∧ (∃ i, (v i).coeff N ≠ 0) ∧
      (∀ f : Polynomial K, (∀ i, f ∣ v i) → IsUnit f) ∧
      IsPrimitiveVec (fun i => homogeneousParameterPolynomialValue (v i) N p q) ∧
      (∀ i, ((v i).homogenize N).IsHomogeneous N) ∧
      ∀ i, H i = g * aeval ![p, q] ((v i).homogenize N) := by
  classical
  have hH0 : H ≠ 0 := by
    intro hz
    have hJ0 : jac H = 0 := by
      funext i j
      simp [hz, jac]
    have hr0 : polyRank (jac H) = 0 := by rw [hJ0]; simp [polyRank]
    omega
  obtain ⟨a, ha⟩ : ∃ a, H a ≠ 0 := by
    simpa only [ne_eq, _root_.funext_iff, Pi.zero_apply, not_forall] using hH0
  obtain ⟨φ, _hφ, ht, _hEuler, p, q, D, hD, hp, hq, hpH, hqH, hrel, htfrac,
    v, r, hv, hvprim, hr, hrep⟩ :=
    homogeneous_rank_two_map_constructs_primitive_projective_parameter_and_source_pencil H hd hH hrank a ha
  have ht' : Transcendental K (algebraMap R₀ (FractionRing R₀) p / algebraMap R₀ (FractionRing R₀) q) :=
    htfrac ▸ ht
  have hrep' : ∀ i, algebraMap R₀ (FractionRing R₀) (H i) =
      r * Polynomial.aeval (algebraMap R₀ (FractionRing R₀) p / algebraMap R₀ (FractionRing R₀) q) (v i) := by
    simpa only [htfrac] using hrep
  obtain ⟨N, g, hN, htop, hg, hprim, hWne, hfactor⟩ :=
    projective_parameter_representation_constructs_primitive_source_polynomial_factorization
      H p q hq hrel v hv hvprim r hr ht' hrep'
  let W : Fin 4 → R₀ := fun i => homogeneousParameterPolynomialValue (v i) N p q
  have hWhom (i) : (W i).IsHomogeneous (D * N) :=
    homogeneous_parameter_value_source_homogeneous (v i) N p q hpH hqH
  have hNpos : 0 < N := by
    by_contra hn
    have hN0 : N = 0 := by omega
    have hWconst (i) : W i = C ((W i).coeff 0) :=
      eq_C_of_isHomogeneous_zero (by simpa only [hN0, mul_zero] using hWhom i)
    have hconst : H = fun i => g * C ((W i).coeff 0) := by
      funext i
      exact (hfactor i).trans (congrArg (g * ·) (hWconst i))
    have hle := polynomial_scalar_constant_vector_jacobian_rank_at_most_one g (fun i => (W i).coeff 0)
    rw [← hconst, hrank] at hle
    omega
  obtain ⟨j, hj⟩ : ∃ j, W j ≠ 0 := by
    simpa only [ne_eq, _root_.funext_iff, Pi.zero_apply, not_forall] using hWne
  have hprod : g * W j ≠ 0 := mul_ne_zero hg hj
  obtain ⟨c, hgc⟩ := isHomogeneous_of_mul_left
    (p := g) (q := W j) (by rw [← hfactor j]; exact hH j) hprod
  have hdegree : c + D * N = d := (hgc.mul (hWhom j)).inj_right
    (by rw [← hfactor j]; exact hH j) hprod
  exact ⟨p, q, g, D, N, c, v, hD, hNpos, hp, hq, hg, hpH, hqH, hgc,
    hdegree, hrel, hN, htop, hvprim, hprim,
    (fun i => Polynomial.isHomogeneous_homogenize (v i)), hfactor⟩

end DimensionFourDependence
