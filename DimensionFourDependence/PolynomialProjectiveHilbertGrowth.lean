import DimensionFourDependence.PolynomialProductDimension
import DimensionFourDependence.ProjectivePointHilbertEvaluation

/-! # Four independent polynomial coordinates force projective Hilbert growth of slope at least three -/

namespace DimensionFourDependence

open MvPolynomial Module

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000

variable {K σ : Type*} [Field K]

/-- Homogeneous evaluation in the actual one-variable polynomial
coordinates, before embedding their values in the rational function field. -/
noncomputable def polynomialHomogeneousEvaluation (p : σ → Polynomial K) (n : ℕ) :
    homogeneousSubmodule σ K n →ₗ[K] Polynomial K :=
  (aeval p).toLinearMap.comp (homogeneousSubmodule σ K n).subtype

/-- Multiplication of homogeneous values respects their total degree. -/
theorem polynomialHomogeneousEvaluation_mul_mem_range
    (p : σ → Polynomial K) (m n : ℕ) (a b : Polynomial K)
    (ha : a ∈ LinearMap.range (polynomialHomogeneousEvaluation p m))
    (hb : b ∈ LinearMap.range (polynomialHomogeneousEvaluation p n)) :
    a * b ∈ LinearMap.range (polynomialHomogeneousEvaluation p (m + n)) := by
  obtain ⟨P, rfl⟩ := ha
  obtain ⟨Q, rfl⟩ := hb
  refine ⟨⟨P.val * Q.val, P.property.mul Q.property⟩, ?_⟩
  change aeval p (P.val * Q.val) = aeval p P.val * aeval p Q.val
  exact map_mul (aeval p) _ _

/-- The polynomial evaluation range computes precisely the same
projective Hilbert function as the corresponding rational coordinates. -/
theorem polynomialHomogeneousEvaluation_rank_eq_projective_hilbert
    (p : σ → Polynomial K) (n : ℕ) :
    finrank K (LinearMap.range (polynomialHomogeneousEvaluation p n)) =
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := K)
        (fun i => algebraMap (Polynomial K) (RatFunc K) (p i))).toIdeal n := by
  let φ := IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K)
  have he : homogeneousPointEvaluation (K := K)
      (fun i => algebraMap (Polynomial K) (RatFunc K) (p i)) n =
      φ.toLinearMap.comp (polynomialHomogeneousEvaluation p n) := by
    ext P
    exact (comp_aeval_apply p φ P.val).symm
  have hk := LinearMap.ker_comp_of_ker_eq_bot (g := φ.toLinearMap)
    (polynomialHomogeneousEvaluation p n)
    (LinearMap.ker_eq_bot.mpr (show Function.Injective φ.toLinearMap from
      IsFractionRing.injective (Polynomial K) (RatFunc K)))
  rw [projectiveHilbertFunction_point_eq_evaluation_rank, he,
    ← (φ.toLinearMap.comp (polynomialHomogeneousEvaluation p n)).quotKerEquivRange.finrank_eq,
    hk, (polynomialHomogeneousEvaluation p n).quotKerEquivRange.finrank_eq]

/-- Four independent coordinate polynomials construct at least
3n+1 independent homogeneous sections in every degree n. -/
theorem independent_four_polynomial_coordinates_hilbert_lower_bound
    (p : Fin 4 → Polynomial K) (hp : LinearIndependent K p) (n : ℕ) :
    3 * n + 1 ≤ projectiveHilbertFunction (projectiveFieldPointIdeal (E := K)
      (fun i => algebraMap (Polynomial K) (RatFunc K) (p i))).toIdeal n := by
  classical
  let W (m : ℕ) := LinearMap.range (polynomialHomogeneousEvaluation p m)
  have hpos (m : ℕ) : 0 < finrank K (W m) := by
    let P : homogeneousSubmodule (Fin 4) K m :=
      ⟨X 0 ^ m, isHomogeneous_X_pow (R := K) 0 m⟩
    have hmem : p 0 ^ m ∈ W m := by
      refine ⟨P, ?_⟩
      change aeval p (X 0 ^ m) = p 0 ^ m
      simp only [map_pow, aeval_X]
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨p 0 ^ m, hmem⟩, ?_⟩
    intro he
    have hz := congrArg Subtype.val he
    exact pow_ne_zero m (hp.ne_zero 0) hz
  have hfirst : 4 ≤ finrank K (W 1) := by
    have hm (i : Fin 4) : p i ∈ W 1 := by
      refine ⟨⟨X i, isHomogeneous_X (R := K) i⟩, ?_⟩
      exact aeval_X p i
    let v : Fin 4 → W 1 := fun i => ⟨p i, hm i⟩
    have hv : LinearIndependent K v := by
      apply LinearIndependent.of_comp (W 1).subtype
      exact hp
    simpa only [Fintype.card_fin] using hv.fintype_card_le_finrank
  have hstep (m : ℕ) : finrank K (W m) + 3 ≤ finrank K (W (m + 1)) := by
    have hb := polynomial_subspace_product_finrank_lower_bound (W 1) (W m) (W (m + 1))
      (hpos 1) (hpos m) (fun a ha b hb => by
        change a * b ∈ LinearMap.range (polynomialHomogeneousEvaluation p (m + 1))
        exact (congrArg (fun k : ℕ => a * b ∈ LinearMap.range
          (polynomialHomogeneousEvaluation p k)) (Nat.add_comm 1 m)).mp
            (polynomialHomogeneousEvaluation_mul_mem_range p 1 m a b ha hb))
    omega
  have hlower : ∀ m, 3 * m + 1 ≤ finrank K (W m) := by
    intro m
    induction m with
    | zero => have := hpos 0; omega
    | succ m ih => have := hstep m; omega
  have he := polynomialHomogeneousEvaluation_rank_eq_projective_hilbert p n
  exact (hlower n).trans_eq he

end DimensionFourDependence
