import DimensionFourDependence.DerivationLineTaylor
import DimensionFourDependence.AffineLinePolynomialRestriction
import DimensionFourDependence.ImageEquationWitness

/-! # Zero acceleration constructs actual polynomial quasi-translations -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 2500000

variable {K F : Type*} [Field K] [Field F] [CharZero F] [Algebra K F] {n : ℕ}

/-- A derivation invariant is constant on the entire polynomial line
when the line's coordinate acceleration vanishes. -/
theorem invariant_polynomial_constant_on_zero_acceleration_line
    (D : Derivation K F F) (y : Fin n → F)
    (hacc : ∀ i, D (D (y i)) = 0) (p : MvPolynomial (Fin n) K)
    (hp : D (aeval y p) = 0) :
    affineLinePolynomialRestriction y (fun i => D (y i)) p = Polynomial.C (aeval y p) := by
  let q := affineLinePolynomialRestriction y (fun i => D (y i)) p
  have he : polynomialCoefficientDerivation D q = q.derivative :=
    aeval_line_coefficient_derivation D y (fun i => D (y i)) (fun _ => rfl) hacc p
  have h0 : q.coeff 0 = aeval y p := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simpa only [mul_zero, add_zero] using
      affineLinePolynomialRestriction_eval y (fun i => D (y i)) 0 p
  change q = Polynomial.C (aeval y p)
  apply sub_eq_zero.mp
  apply polynomial_zero_of_coefficient_derivation_eq_derivative D
  · simp only [map_sub, he, polynomialCoefficientDerivation_C, hp, map_zero,
      sub_zero, Polynomial.derivative_sub, Polynomial.derivative_C]
  · simp only [Polynomial.coeff_sub, h0, Polynomial.coeff_C_zero, sub_self]

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
local notation "P₀" => MvPolynomial (Fin n) K
local notation "F₀" => FractionRing (MvPolynomial (Fin n) K)

/-- Substitution by the actual polynomial map `X+s u`. -/
noncomputable def polynomialDirectionTranslation (u : Fin n → P₀) (s : K) : P₀ →ₐ[K] P₀ :=
  aeval (fun i => X i + C s * u i)

theorem polynomialDirectionTranslation_X (u : Fin n → P₀) (s : K) (i : Fin n) :
    polynomialDirectionTranslation u s (X i) = X i + C s * u i := aeval_X _ _

/-- Every polynomial Jacobian-kernel map is constant on the full
formal-parameter line of a zero-acceleration direction. -/
theorem zero_acceleration_polynomial_kernel_map_line_identity
    (u : Fin n → P₀) (hacc : jac u *ᵥ u = 0)
    (H : Fin n → P₀) (hker : jac H *ᵥ u = 0) (i : Fin n) :
    affineLinePolynomialRestriction (rationalCoordinate (K := K))
      (fun j => algebraMap P₀ F₀ (u j)) (H i) = Polynomial.C (algebraMap P₀ F₀ (H i)) := by
  classical
  let U : Fin n → F₀ := fun j => algebraMap P₀ F₀ (u j)
  let D := sourceVectorDerivation U
  have hD (V : Fin n → P₀) (hV : jac V *ᵥ u = 0) (j : Fin n) :
      D (algebraMap P₀ F₀ (V j)) = 0 := by
    have he := congrArg (algebraMap P₀ F₀) (congrFun hV j)
    simpa only [D, sourceVectorDerivation_apply, rationalPartial_polynomial, U,
      Matrix.mulVec, dotProduct, jac, Matrix.of_apply, map_sum, map_mul,
      Pi.zero_apply, map_zero, mul_comm] using he
  have hDy (j : Fin n) : D (rationalCoordinate (K := K) j) = U j :=
    sourceVectorDerivation_coordinate U j
  have hD2 (j : Fin n) : D (D (rationalCoordinate (K := K) j)) = 0 := by
    rw [hDy]
    exact hD u hacc j
  have hp : D (aeval (rationalCoordinate (K := K)) (H i)) = 0 := by
    have he := aeval_polynomial_to_fraction (fun j : Fin n => (X j : P₀)) (H i)
    simp only [aeval_X_left_apply] at he
    change algebraMap P₀ F₀ (H i) = aeval (rationalCoordinate (K := K)) (H i) at he
    rw [← he]
    exact hD H hker i
  have hline := invariant_polynomial_constant_on_zero_acceleration_line D
    (rationalCoordinate (K := K)) hD2 (H i) hp
  have heval : aeval (rationalCoordinate (K := K)) (H i) = algebraMap P₀ F₀ (H i) := by
    change aeval (fun j : Fin n => algebraMap P₀ F₀ (X j)) (H i) = algebraMap P₀ F₀ (H i)
    simpa only [aeval_X_left_apply] using
      (aeval_polynomial_to_fraction (fun j : Fin n => (X j : P₀)) (H i)).symm
  have hvel : (fun j => D (rationalCoordinate (K := K) j)) = U := funext hDy
  rw [hvel, heval] at hline
  exact hline

/-- Zero acceleration makes every original polynomial Jacobian-kernel
map invariant under every parameter translation, without field extension
or pointwise interpretation in the conclusion. -/
theorem zero_acceleration_polynomial_translation_preserves_kernel_map
    (u : Fin n → P₀) (hacc : jac u *ᵥ u = 0)
    (H : Fin n → P₀) (hker : jac H *ᵥ u = 0) (s : K) (i : Fin n) :
    polynomialDirectionTranslation u s (H i) = H i := by
  have hline := zero_acceleration_polynomial_kernel_map_line_identity u hacc H hker i
  have hlinet := congrArg (Polynomial.aeval (algebraMap K F₀ s)) hline
  rw [affineLinePolynomialRestriction_aeval, Polynomial.aeval_C] at hlinet
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hlinet
  apply IsFractionRing.injective P₀ F₀
  change algebraMap P₀ F₀ (aeval (fun j => X j + C s * u j) (H i)) = _
  rw [aeval_polynomial_to_fraction]
  have hpoint : (fun j => algebraMap P₀ F₀ (X j + C s * u j)) =
      (fun j => rationalCoordinate (K := K) j + algebraMap P₀ F₀ (u j) * algebraMap K F₀ s) := by
    funext j
    have hCs : algebraMap P₀ F₀ (C s) = algebraMap K F₀ s :=
      (IsScalarTower.algebraMap_apply K P₀ F₀ s).symm
    simp only [map_add, map_mul, hCs]
    change rationalCoordinate (K := K) j + algebraMap K F₀ s * algebraMap P₀ F₀ (u j) =
      rationalCoordinate (K := K) j + algebraMap P₀ F₀ (u j) * algebraMap K F₀ s
    ring
  rw [hpoint]
  exact hlinet

/-- In particular, the direction itself is unchanged by its translations. -/
theorem zero_acceleration_polynomial_translation_preserves_direction
    (u : Fin n → P₀) (hacc : jac u *ᵥ u = 0) (s : K) (i : Fin n) :
    polynomialDirectionTranslation u s (u i) = u i :=
  zero_acceleration_polynomial_translation_preserves_kernel_map u hacc u hacc s i

/-- The actual polynomial substitutions satisfy the additive parameter law. -/
theorem zero_acceleration_polynomial_translation_comp
    (u : Fin n → P₀) (hacc : jac u *ᵥ u = 0) (s t : K) :
    (polynomialDirectionTranslation u s).comp (polynomialDirectionTranslation u t) =
      polynomialDirectionTranslation u (s + t) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, polynomialDirectionTranslation_X, map_add, map_mul,
    show polynomialDirectionTranslation u s (C t) = C t from aeval_C _ _,
    zero_acceleration_polynomial_translation_preserves_direction u hacc, map_add]
  ring

theorem polynomialDirectionTranslation_zero (u : Fin n → P₀) :
    polynomialDirectionTranslation u 0 = AlgHom.id K P₀ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [polynomialDirectionTranslation_X, map_zero, zero_mul, add_zero, AlgHom.id_apply]

/-- Zero acceleration constructs the polynomial automorphism with
inverse `X-s u`, the quasi-translation required in Proposition 2.1. -/
noncomputable def zeroAccelerationPolynomialTranslationEquiv
    (u : Fin n → P₀) (hacc : jac u *ᵥ u = 0) (s : K) : P₀ ≃ₐ[K] P₀ :=
  AlgEquiv.ofAlgHom (polynomialDirectionTranslation u s) (polynomialDirectionTranslation u (-s))
    (by rw [zero_acceleration_polynomial_translation_comp u hacc, add_neg_cancel,
      polynomialDirectionTranslation_zero])
    (by rw [zero_acceleration_polynomial_translation_comp u hacc, neg_add_cancel,
      polynomialDirectionTranslation_zero])

end DimensionFourDependence
