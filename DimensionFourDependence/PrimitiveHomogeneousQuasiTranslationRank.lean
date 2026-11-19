import DimensionFourDependence.ZeroAccelerationPolynomialTranslation
import DimensionFourDependence.HomogeneousAffineLeadingCoefficient
import DimensionFourDependence.PrimitiveVectorGenericAvoidance
import DimensionFourDependence.OutputSelection

/-! # The primitive positive homogeneous quasi-translation direction has rank two

The highest formal-parameter coefficient gives self-vanishing of the
direction. Its image relation prime therefore contains the entire
primitive vector, and the checked common-zero dimension bound excludes
rank three. This is the primitive four-dimensional case of de Bondt,
Quasi-translations and singular Hessians, Theorem 5.2.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2500000

variable {K : Type u} [Field K] [CharZero K] {n : ℕ}
local notation "P₀" => MvPolynomial (Fin n) K
local notation "F₀" => FractionRing (MvPolynomial (Fin n) K)

/-- The positive homogeneous part of any polynomial invariant vanishes
on the direction itself: extract its top formal line coefficient. -/
theorem homogeneous_zero_acceleration_kernel_map_vanishes_on_direction
    (u : Fin n → P₀) (hacc : jac u *ᵥ u = 0)
    (H : Fin n → P₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hker : jac H *ᵥ u = 0) (i : Fin n) : aeval u (H i) = 0 := by
  have he := congrArg (fun p : Polynomial F₀ => p.coeff d)
    (zero_acceleration_polynomial_kernel_map_line_identity u hacc H hker i)
  change (aeval (fun j => Polynomial.C (rationalCoordinate (K := K) j) +
    Polynomial.C (algebraMap P₀ F₀ (u j)) * Polynomial.X) (H i)).coeff d = _ at he
  rw [homogeneous_affine_line_coefficient_at_degree (H i) (hH i)] at he
  have he0 : aeval (fun j => algebraMap P₀ F₀ (u j)) (H i) = 0 := by
    simpa only [Polynomial.coeff_C, if_neg hd.ne'] using he
  apply IsFractionRing.injective P₀ F₀
  rw [map_zero, aeval_polynomial_to_fraction]
  exact he0

/-- The homogeneous quasi-translation direction vanishes on its own
polynomial image, the self-vanishing identity used in classification. -/
theorem homogeneous_quasi_translation_vanishes_on_its_own_image
    (u : Fin n → P₀) {e : ℕ} (he : 0 < e) (hu : IsHomogMap u e)
    (hacc : jac u *ᵥ u = 0) : ∀ i, aeval u (u i) = 0 :=
  homogeneous_zero_acceleration_kernel_map_vanishes_on_direction u hacc u he hu hacc

/-- Self-vanishing persists at every original source point in any
extension field, without a genericity or nonzero-point assumption. -/
theorem homogeneous_quasi_translation_image_point_is_common_zero
    (u : Fin n → P₀) {e : ℕ} (he : 0 < e) (hu : IsHomogMap u e)
    (hacc : jac u *ᵥ u = 0)
    {E : Type*} [Field E] [Algebra K E] (z : Fin n → E) (i : Fin n) :
    aeval (fun j => aeval z (u j)) (u i) = 0 := by
  rw [← comp_aeval_apply u (aeval z) (u i),
    homogeneous_quasi_translation_vanishes_on_its_own_image u he hu hacc, map_zero]

local notation "R₀" => MvPolynomial (Fin 4) K
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- A primitive nonzero homogeneous zero-acceleration direction in
four variables has rank at most two. The actual image prime and its
dimension contradiction are constructed internally. -/
theorem primitive_positive_homogeneous_quasi_translation_rank_at_most_two
    (u : Fin 4 → R₀) {e : ℕ} (he : 0 < e) (hUne : u ≠ 0)
    (hhom : IsHomogMap u e) (hprim : IsPrimitiveVec u) (hacc : jac u *ᵥ u = 0) :
    polyRank (jac u) ≤ 2 := by
  have hrlt : polyRank (jac u) < 4 := by
    have hleft : u ᵥ* (jac u)ᵀ = 0 := by simpa only [Matrix.vecMul_transpose] using hacc
    have hr := polyRank_lt_of_vecMul_eq_zero (jac u)ᵀ u hUne hleft
    simpa only [polyRank, Matrix.transpose_map, Matrix.rank_transpose] using hr
  by_contra hn
  have hrank : polyRank (jac u) = 3 := by omega
  let U : Fin 4 → S₀ := fun i => algebraMap R₀ S₀ (u i)
  have hrU : (rationalJacobian U).rank = 3 := by
    rw [rationalJacobian_polynomial]
    exact hrank
  obtain ⟨s, _hs, hUind, _hAlg⟩ := exists_independent_output_triple U hrU
  let I := fiberVanishingIdeal (L := K) U
  have hmem (i : Fin 4) : u i ∈ I := by
    change aeval U (u i) = 0
    rw [← aeval_polynomial_to_fraction,
      homogeneous_quasi_translation_vanishes_on_its_own_image u he hhom hacc, map_zero]
  have hlt := primitive_nonzero_vector_common_zero_prime_trdeg_lt_three u hUne hprim I hmem
  let f : (R₀ ⧸ I) →ₐ[K] S₀ := Ideal.kerLiftAlg (aeval U : R₀ →ₐ[K] S₀)
  let y : Fin 3 → R₀ ⧸ I := fun i => Ideal.Quotient.mk I (X (s i))
  have hy : AlgebraicIndependent K y := by
    apply AlgebraicIndependent.of_comp f
    have hf : f ∘ y = fun i => U (s i) := by
      funext i
      exact (Ideal.kerLiftAlg_mk (aeval U : R₀ →ₐ[K] S₀) (X (s i))).trans (aeval_X U (s i))
    rwa [hf]
  have hge : 3 ≤ Algebra.trdeg K (R₀ ⧸ I) := by simpa using hy.lift_cardinalMk_le_trdeg
  exact not_le_of_gt hlt hge

/-- The actual nonzero primitive positive homogeneous direction of
Proposition 2.1 has Jacobian rank exactly two. No rank of the direction
or auxiliary image equation is supplied as a hypothesis. -/
theorem primitive_positive_homogeneous_quasi_translation_rank_two
    (u : Fin 4 → R₀) {e : ℕ} (he : 0 < e) (hUne : u ≠ 0)
    (hhom : IsHomogMap u e) (hprim : IsPrimitiveVec u) (hacc : jac u *ᵥ u = 0) :
    polyRank (jac u) = 2 :=
  le_antisymm
    (primitive_positive_homogeneous_quasi_translation_rank_at_most_two u he hUne hhom hprim hacc)
    (two_le_polyRank_jac_of_isPrimitiveVec u he hUne hhom hprim)

end DimensionFourDependence
