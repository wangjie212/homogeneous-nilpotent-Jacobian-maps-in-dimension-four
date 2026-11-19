import DimensionFourDependence.ProjectivePointHilbertEvaluation

/-! # A genuine transcendental projective coordinate forces linear Hilbert growth -/

namespace DimensionFourDependence

open MvPolynomial Module

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K F σ : Type*} [Field K] [Field F] [Algebra K F] [Finite σ]

/-- A specified unit frame and transcendental original coordinate
give n+1 independent actual degree-n projective sections. -/
theorem projective_point_hilbert_lower_bound_of_unit_frame_and_transcendental
    (x : σ → F) (a i : σ) (ha : x a = 1) (hi : Transcendental K (x i)) (n : ℕ) :
    n + 1 ≤ projectiveHilbertFunction (projectiveFieldPointIdeal (E := K) x).toIdeal n := by
  have hpow : LinearIndependent K (fun k : ℕ => x i ^ k) := by
    have he := (Polynomial.basisMonomials K).linearIndependent.map'
      (Polynomial.aeval (x i)).toLinearMap (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hi))
    simpa only [Function.comp_def, Polynomial.coe_basisMonomials, AlgHom.toLinearMap_apply, Polynomial.aeval_monomial, map_one, one_mul] using he
  let P (k : Fin (n + 1)) : homogeneousSubmodule σ K n :=
    ⟨X i ^ (k : ℕ) * X a ^ (n - k), by
      change (X i ^ (k : ℕ) * X a ^ (n - k) : MvPolynomial σ K).IsHomogeneous n
      have hh := (isHomogeneous_X_pow (R := K) i (k : ℕ)).mul
        (isHomogeneous_X_pow (R := K) a (n - k))
      convert hh using 1
      omega⟩
  let ev := homogeneousPointEvaluation (K := K) x n
  let v : Fin (n + 1) → LinearMap.range ev := fun k => ⟨ev (P k), ⟨P k, rfl⟩⟩
  have hv : LinearIndependent K v := by
    apply LinearIndependent.of_comp (LinearMap.range ev).subtype
    have he := hpow.comp (fun k : Fin (n + 1) => (k : ℕ)) Fin.val_injective
    convert he using 1
    funext k
    change aeval x (X i ^ (k : ℕ) * X a ^ (n - k)) = x i ^ (k : ℕ)
    simp only [map_mul, map_pow, aeval_X, ha, one_pow, mul_one]
  rw [projectiveHilbertFunction_point_eq_evaluation_rank]
  simpa only [Fintype.card_fin] using hv.fintype_card_le_finrank

end DimensionFourDependence
