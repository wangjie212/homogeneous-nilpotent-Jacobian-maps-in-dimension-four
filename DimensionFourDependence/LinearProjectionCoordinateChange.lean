import DimensionFourDependence.LinearMonicProjectionChoice

/-! # Actual affine coordinates for the constructed linear projection

The chosen linear automorphism gives a polynomial algebra equivalence.
Its inverse evaluates to actual elements of any original affine algebra.
These elements retain the original generation and every equation, so the
projection direction is a coordinate change of the original surface.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k : Type*} [Field k] {n : ℕ}

/-- The inverse linear polynomial change recovers every original
polynomial, as an identity over the original coefficient field. -/
theorem linearPolynomialPullback_inverse
    (T : (Fin n → k) ≃ₗ[k] (Fin n → k)) (f : MvPolynomial (Fin n) k) :
    linearPolynomialPullback (LinearMap.toMatrix' T.symm.toLinearMap)
      (linearPolynomialPullback (LinearMap.toMatrix' T.toLinearMap) f) = f := by
  let P := LinearMap.toMatrix' T.toLinearMap
  let Q := LinearMap.toMatrix' T.symm.toLinearMap
  have hmul : P * Q = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have hcomp : T.toLinearMap.comp T.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact T.apply_symm_apply x
    rw [hcomp, LinearMap.toMatrix'_id]
  have htranspose : Q.transpose * P.transpose = 1 := by
    rw [← Matrix.transpose_mul, hmul, Matrix.transpose_one]
  change aeval (fun i : Fin n => ∑ j : Fin n, C (Q i j) * X j)
    (aeval (fun i : Fin n => ∑ j : Fin n, C (P i j) * X j) f) = f
  simpa only [Matrix.transpose_apply] using
    aeval_aeval_linear_of_mul_eq_one P.transpose Q.transpose htranspose f

/-- The actual polynomial algebra equivalence of an invertible linear
coordinate change, including its constructed polynomial inverse. -/
noncomputable def linearPolynomialCoordinateEquiv
    (T : (Fin n → k) ≃ₗ[k] (Fin n → k)) :
    MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k :=
  AlgEquiv.ofAlgHom (aeval (linearPolynomialMap (LinearMap.toMatrix' T.toLinearMap)))
    (aeval (linearPolynomialMap (LinearMap.toMatrix' T.symm.toLinearMap)))
    (by
      apply AlgHom.ext
      intro f
      exact linearPolynomialPullback_inverse T.symm f)
    (by
      apply AlgHom.ext
      intro f
      exact linearPolynomialPullback_inverse T f)

/-- The equivalence's forward value is the original linear pullback. -/
theorem linearPolynomialCoordinateEquiv_apply
    (T : (Fin n → k) ≃ₗ[k] (Fin n → k)) (f : MvPolynomial (Fin n) k) :
    linearPolynomialCoordinateEquiv T f =
      linearPolynomialPullback (LinearMap.toMatrix' T.toLinearMap) f := rfl

variable {A : Type*} [CommRing A] [Algebra k A]

/-- New affine coordinates are actual linear functions of the original
generators, obtained by evaluating the constructed inverse substitution. -/
noncomputable def linearProjectionCoordinate
    (T : (Fin n → k) ≃ₗ[k] (Fin n → k)) (x : Fin n → A) (i : Fin n) : A :=
  aeval x ((linearPolynomialCoordinateEquiv T).symm (X i))

/-- Evaluation in the new coordinates is evaluation of the inverse
substitution in the original affine algebra. -/
theorem aeval_linearProjectionCoordinate
    (T : (Fin n → k) ≃ₗ[k] (Fin n → k)) (x : Fin n → A) :
    aeval (linearProjectionCoordinate T x) =
      (aeval x).comp (linearPolynomialCoordinateEquiv T).symm.toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [aeval_X, AlgHom.comp_apply, linearProjectionCoordinate, AlgEquiv.coe_toAlgHom]

/-- The changed equation has exactly the original value in the actual
affine algebra, for every original polynomial and coefficient extension. -/
theorem linearProjectionCoordinate_eval_transformed
    (T : (Fin n → k) ≃ₗ[k] (Fin n → k)) (x : Fin n → A)
    (f : MvPolynomial (Fin n) k) :
    aeval (linearProjectionCoordinate T x)
      (linearPolynomialPullback (LinearMap.toMatrix' T.toLinearMap) f) = aeval x f := by
  rw [aeval_linearProjectionCoordinate]
  change aeval x ((linearPolynomialCoordinateEquiv T).symm (linearPolynomialCoordinateEquiv T f)) = _
  rw [AlgEquiv.symm_apply_apply]

/-- The actual coordinate change preserves generation of the entire
original affine algebra, without an assumed generation statement for the
new coordinates. -/
theorem linearProjectionCoordinate_adjoin_eq_top
    (T : (Fin n → k) ≃ₗ[k] (Fin n → k)) (x : Fin n → A)
    (hx : Algebra.adjoin k (Set.range x) = ⊤) :
    Algebra.adjoin k (Set.range (linearProjectionCoordinate T x)) = ⊤ := by
  let y := linearProjectionCoordinate T x
  have hmem (i : Fin n) : x i ∈ Algebra.adjoin k (Set.range y) := by
    have hp : aeval y (linearPolynomialPullback (LinearMap.toMatrix' T.toLinearMap) (X i)) ∈
        Algebra.adjoin k (Set.range y) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨_, rfl⟩
    have heq : aeval y (linearPolynomialPullback (LinearMap.toMatrix' T.toLinearMap) (X i)) = x i := by
      simpa only [aeval_X] using linearProjectionCoordinate_eval_transformed T x (X i)
    rwa [heq] at hp
  apply top_unique
  rw [← hx]
  apply Algebra.adjoin_le_iff.mpr
  rintro _ ⟨i, rfl⟩
  exact hmem i

end DimensionFourDependence
