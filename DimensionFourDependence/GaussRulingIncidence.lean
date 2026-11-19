import DimensionFourDependence.GaussCharacteristicSubspaces
import DimensionFourDependence.RectangularJacobianRank

/-! # The actual image point lies in its Gauss ruling

The constructed rational Gauss parameter is realized in the original
source function field. Its nonzero differential, the rational chain
rule, and Euler's identity show that both the normalized normal and its
parameter derivative annihilate the actual image point.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- A transcendental source rational function has a nonzero coordinate
partial derivative in characteristic zero. -/
theorem exists_rationalPartial_ne_zero_of_transcendental {n : ℕ}
    (t : FractionRing (MvPolynomial (Fin n) K)) (ht : Transcendental K t) :
    ∃ j, rationalPartial (K := K) j t ≠ 0 := by
  by_contra hn
  push Not at hn
  let Y : Fin 1 → FractionRing (MvPolynomial (Fin n) K) := fun _ => t
  have hY : AlgebraicIndependent K Y :=
    (algebraicIndependent_singleton_iff (R := K) (x := Y) 0).mpr ht
  have hr := rationalJacobian_rank_of_independent Y hY
  have hz : rationalJacobian Y = 0 := by
    ext i j
    exact hn j
  rw [hz, Matrix.rank_zero] at hr
  exact Nat.zero_ne_one hr

/-- The actual realization of any rational parameter of the Gauss field. -/
noncomputable def gaussParameterSourceHom
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) :
    RatFunc K →ₐ[K] FractionRing (MvPolynomial (Fin 4) K) :=
  (projectiveRatioField (K := K) (rationalImageNormal H I.equation)
    (imageNormalPivot H I)).val.comp e.toAlgHom

/-- The actual normalized normal written in the chosen rational Gauss parameter. -/
noncomputable def gaussParameterNormal
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) : Fin 4 → RatFunc K :=
  fun i => e.symm (fullOutputCoordinate (K := K)
    (fun j => rationalImageNormal H I.equation j /
      rationalImageNormal H I.equation (imageNormalPivot H I)) i)

omit [CharZero K] in
/-- Realizing the parameter-normal coordinates recovers the actual ratios. -/
theorem gaussParameterSourceHom_normal
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) (i : Fin 4) :
    gaussParameterSourceHom H I e (gaussParameterNormal H I e i) =
      rationalImageNormal H I.equation i /
        rationalImageNormal H I.equation (imageNormalPivot H I) := by
  let M := projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)
  let x : Fin 4 → M := fullOutputCoordinate (K := K)
    (fun j => rationalImageNormal H I.equation j /
      rationalImageNormal H I.equation (imageNormalPivot H I))
  change M.val (e (e.symm (x i))) = _
  rw [e.apply_symm_apply]
  rfl

omit [CharZero K] in
/-- The actual Gauss parameter is transcendental in the original source field. -/
theorem gaussParameterSourceHom_X_transcendental
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) :
    Transcendental K (gaussParameterSourceHom H I e RatFunc.X) := by
  intro ha
  exact RatFunc.transcendental_X
    ((isAlgebraic_algHom_iff (gaussParameterSourceHom H I e)
      (gaussParameterSourceHom H I e).injective).mp ha)

/-- The actual normalized image normal annihilates the actual output point. -/
theorem ImageRelationWitness.normalized_normal_dot_output_eq_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hH : IsHomogMap H d) (I : ImageRelationWitness H) :
    (fun i => rationalImageNormal H I.equation i /
      rationalImageNormal H I.equation (imageNormalPivot H I)) ⬝ᵥ
      (fun i => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H i)) = 0 := by
  have hp := left_normal_dot_eq_zero H (imageRelationNormal H I.equation) hd.ne' hH (I.left_kernel H)
  have hf := congrArg (algebraMap (MvPolynomial (Fin 4) K)
    (FractionRing (MvPolynomial (Fin 4) K))) hp
  simp only [map_sum, map_mul, map_zero] at hf
  simp only [dotProduct, div_mul_eq_mul_div, ← Finset.sum_div]
  change (∑ i, algebraMap (MvPolynomial (Fin 4) K)
    (FractionRing (MvPolynomial (Fin 4) K)) (imageRelationNormal H I.equation i) *
      algebraMap (MvPolynomial (Fin 4) K) _ (H i)) / _ = 0
  rw [hf, zero_div]

omit [CharZero K] in
/-- The normalized actual normal annihilates every actual source tangent. -/
theorem ImageRelationWitness.normalized_normal_dot_output_partial_eq_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H) (j : Fin 4) :
    (fun i => rationalImageNormal H I.equation i /
      rationalImageNormal H I.equation (imageNormalPivot H I)) ⬝ᵥ
      (fun i => rationalPartial (K := K) j
        (algebraMap (MvPolynomial (Fin 4) K)
          (FractionRing (MvPolynomial (Fin 4) K)) (H i))) = 0 := by
  have hk := congrFun (imageRelationNormal_rational_left_kernel H I.equation I.vanishing) j
  simp only [vecMul, dotProduct, Matrix.map_apply, jac, of_apply, Pi.zero_apply] at hk
  simp only [dotProduct, rationalPartial_polynomial, div_mul_eq_mul_div, ← Finset.sum_div]
  change (∑ i, algebraMap (MvPolynomial (Fin 4) K)
    (FractionRing (MvPolynomial (Fin 4) K)) (imageRelationNormal H I.equation i) *
      algebraMap (MvPolynomial (Fin 4) K) _ (pderiv j (H i))) / _ = 0
  rw [hk, zero_div]

/-- The parameter derivative of the actual normalized normal also
annihilates the actual output point. The parameter's nonzero differential
is proved, rather than assumed. -/
theorem ImageRelationWitness.parameter_normal_derivative_dot_output_eq_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hH : IsHomogMap H d) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) :
    (fun i => gaussParameterSourceHom H I e
      (rationalParameterDerivative K (gaussParameterNormal H I e i))) ⬝ᵥ
      (fun i => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H i)) = 0 := by
  let f := gaussParameterSourceHom H I e
  let w := gaussParameterNormal H I e
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) := fun i => algebraMap _ _ (H i)
  obtain ⟨j, hj⟩ := exists_rationalPartial_ne_zero_of_transcendental (f RatFunc.X)
    (gaussParameterSourceHom_X_transcendental H I e)
  have he : (fun i => f (w i)) ⬝ᵥ Q = 0 := by
    simpa only [f, w, gaussParameterSourceHom_normal] using I.normalized_normal_dot_output_eq_zero H hd hH
  have ht : (fun i => f (w i)) ⬝ᵥ (fun i => rationalPartial (K := K) j (Q i)) = 0 := by
    simpa only [f, w, gaussParameterSourceHom_normal] using I.normalized_normal_dot_output_partial_eq_zero H j
  have hh := congrArg (rationalPartial (K := K) j) he
  rw [derivation_dotProduct, ht, add_zero, map_zero] at hh
  have hchain : (fun i => rationalPartial (K := K) j (f (w i))) =
      (fun i => f (rationalParameterDerivative K (w i)) *
        rationalPartial (K := K) j (f RatFunc.X)) :=
    funext fun i => rational_parameter_chain_rule f (rationalPartial (K := K) j) (w i)
  rw [hchain] at hh
  have hc : ((fun i => f (rationalParameterDerivative K (w i))) ⬝ᵥ Q) *
      rationalPartial (K := K) j (f RatFunc.X) = 0 := by
    rw [dotProduct, Finset.sum_mul]
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact (mul_eq_zero.mp hc).resolve_right hj

/-- The genuine output point lies in the scalar-extended kernel of the
first two actual Gauss normal covectors. -/
theorem ImageRelationWitness.output_mem_parameter_ruling
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hH : IsHomogMap H d) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) :
    (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i)) ∈
      LinearMap.ker (((normalRulingMatrix (rationalParameterDerivative K)
        (gaussParameterNormal H I e)).map (gaussParameterSourceHom H I e)).toLin') := by
  change ((normalRulingMatrix (rationalParameterDerivative K) (gaussParameterNormal H I e)).map
    (gaussParameterSourceHom H I e)) *ᵥ
      (fun i => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H i)) = 0
  funext r
  fin_cases r
  · change (fun i => gaussParameterSourceHom H I e (gaussParameterNormal H I e i)) ⬝ᵥ
      (fun i => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H i)) = 0
    simpa only [gaussParameterSourceHom_normal] using I.normalized_normal_dot_output_eq_zero H hd hH
  · exact I.parameter_normal_derivative_dot_output_eq_zero H hd hH e

end DimensionFourDependence
