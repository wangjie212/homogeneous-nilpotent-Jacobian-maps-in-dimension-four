import DimensionFourDependence.FiberJacobian
import DimensionFourDependence.NilpotentKernel

/-! # The first fiber invariant in equation (2.2)

The tangent-frame identity is derived from nilpotence and rank three of the
actual full Jacobian. The invariant uses the uniquely extended coordinate
derivatives on the actual relative algebraic closure. The independent output
triple and the algebraicity of the last output are still explicit inputs.
-/

namespace DimensionFourDependence

open Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- The first expression `c = x₄ - (∇h)ᵀx` of (2.2). -/
noncomputable def firstFiberInvariant
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) : FractionRing (MvPolynomial (Fin 4) K) :=
  rationalCoordinate (K := K) 3 - ∑ i : Fin 3,
    (coefficientPartial (K := K) Y hY i h : FractionRing (MvPolynomial (Fin 4) K)) *
      rationalCoordinate (K := K) i.castSucc

/-- A tangent derivation kills every coefficient in `L`. -/
theorem tangent_derivation_kills_coefficients
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K))
    (u : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hker : rationalJacobian Y *ᵥ u = 0) (a : coefficientField (K := K) Y) :
    sourceVectorDerivation u (a : FractionRing (MvPolynomial (Fin 4) K)) = 0 :=
  vertical_derivation_kills_coefficient_field Y (sourceVectorDerivation u)
    (sourceVectorDerivation_vertical Y u hker) a

/-- Under the tangent-frame identity, the first expression is a constant
of the actual nonzero vertical derivation. -/
theorem firstFiberInvariant_deriv_zero
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (u : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hker : rationalJacobian Y *ᵥ u = 0) (h : coefficientField (K := K) Y)
    (hframe : u 3 = ∑ i : Fin 3,
      (coefficientPartial (K := K) Y hY i h : FractionRing (MvPolynomial (Fin 4) K)) * u i.castSucc) :
    sourceVectorDerivation u (firstFiberInvariant Y hY h) = 0 := by
  unfold firstFiberInvariant
  rw [map_sub, map_sum, sourceVectorDerivation_coordinate]
  have hs : (∑ i : Fin 3, sourceVectorDerivation u
      ((coefficientPartial (K := K) Y hY i h : FractionRing (MvPolynomial (Fin 4) K)) *
        rationalCoordinate (K := K) i.castSucc)) =
      ∑ i : Fin 3, (coefficientPartial (K := K) Y hY i h : FractionRing (MvPolynomial (Fin 4) K)) *
        u i.castSucc := by
    apply Finset.sum_congr rfl
    intro i _
    rw [(sourceVectorDerivation u).leibniz,
      tangent_derivation_kills_coefficients Y u hker,
      sourceVectorDerivation_coordinate, smul_zero, add_zero]
    rfl
  rw [hs, ← hframe, sub_self]

/-- Membership `c ∈ L` asserted in Lemma 2.2, obtained from the established
constant-field theorem, with the frame condition still explicit. -/
theorem firstFiberInvariant_mem_coefficientField
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (u : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (hu : u ≠ 0)
    (hker : rationalJacobian Y *ᵥ u = 0) (h : coefficientField (K := K) Y)
    (hframe : u 3 = ∑ i : Fin 3,
      (coefficientPartial (K := K) Y hY i h : FractionRing (MvPolynomial (Fin 4) K)) * u i.castSucc) :
    firstFiberInvariant Y hY h ∈ coefficientField (K := K) Y := by
  change firstFiberInvariant Y hY h ∈ (coefficientField (K := K) Y).restrictScalars K
  rw [← tangent_derivation_constants Y hY u hu hker]
  exact firstFiberInvariant_deriv_zero Y hY u hker h hframe

/-- Nilpotence and rank three force the tangent-frame identity used in
the proof of Lemma 2.2. -/
theorem fiber_tangent_frame_of_nilpotent_rank_three
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y)
    (hN : IsNilpotent (rationalJacobian (Fin.snoc Y
      (h : FractionRing (MvPolynomial (Fin 4) K)))))
    (hrank : (rationalJacobian (Fin.snoc Y
      (h : FractionRing (MvPolynomial (Fin 4) K)))).rank = 3)
    (u : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hu : rationalJacobian (Fin.snoc Y
      (h : FractionRing (MvPolynomial (Fin 4) K))) *ᵥ u = 0) :
    u 3 = ∑ i : Fin 3,
      (coefficientPartial (K := K) Y hY i h : FractionRing (MvPolynomial (Fin 4) K)) *
        u i.castSucc := by
  have hd := matrix_nilpotent_kernel_dot_zero _ hN (by decide) (by omega)
    (fiberNormal Y hY h) u (fiberNormal_jacobian_zero Y hY h) hu
  change (∑ i : Fin 4, fiberNormal Y hY h i * u i) = 0 at hd
  rw [Fin.sum_univ_castSucc] at hd
  simp only [fiberNormal, Fin.snoc_castSucc, Fin.snoc_last, neg_mul,
    Finset.sum_neg_distrib, one_mul, fiberGradient] at hd
  change -(∑ i : Fin 3,
    (coefficientPartial (K := K) Y hY i h : FractionRing (MvPolynomial (Fin 4) K)) *
      u i.castSucc) + u 3 = 0 at hd
  linear_combination hd

/-- The first expression of (2.2) belongs to `L` under the actual
nilpotent rank-three Jacobian hypotheses. No tangent vector or frame
identity is supplied as an extra hypothesis. -/
theorem firstFiberInvariant_mem_of_nilpotent_rank_three
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y)
    (hN : IsNilpotent (rationalJacobian (Fin.snoc Y
      (h : FractionRing (MvPolynomial (Fin 4) K)))))
    (hrank : (rationalJacobian (Fin.snoc Y
      (h : FractionRing (MvPolynomial (Fin 4) K)))).rank = 3) :
    firstFiberInvariant Y hY h ∈ coefficientField (K := K) Y := by
  obtain ⟨u, hu0, hu⟩ := matrix_nilpotent_exists_nonzero_kernel _ hN (by omega)
  have hker : rationalJacobian Y *ᵥ u = 0 := by
    funext i
    have hi := congrFun hu i.castSucc
    simpa [rationalJacobian_snoc, mulVec, dotProduct, Fin.snoc] using hi
  exact firstFiberInvariant_mem_coefficientField Y hY u hu0 hker h
    (fiber_tangent_frame_of_nilpotent_rank_three Y hY h hN hrank u hu)

end DimensionFourDependence
