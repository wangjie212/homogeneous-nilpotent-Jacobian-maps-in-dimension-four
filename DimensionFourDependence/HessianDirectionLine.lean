import DimensionFourDependence.CoordinateHessianDirection
import DimensionFourDependence.DerivationLineTaylor

/-! # Integrating normalized Hessian-isotropic directions to image lines

This is the differential-to-line step of Proposition 3.1. The quadratic
and cubic self-contractions, rank-two Hessian, radial radical and chart
normalization imply zero acceleration and the exact line identity.
-/

namespace DimensionFourDependence

open Matrix

variable {K F : Type*} [Field K] [Field F] [CharZero F] [Algebra K F]

/-- A normalized direction satisfying (3.4) has zero acceleration on
the graph coordinates `(Y,h)`. -/
theorem normalized_hessian_graph_zero_acceleration
    (δ : Fin 3 → Derivation K F F) (hcomm : ∀ i j a, δ i (δ j a) = δ j (δ i a))
    (Y : Fin 3 → F) (hcoord : ∀ i j, δ i (Y j) = if j = i then 1 else 0)
    (h : F) (hrank : (derivationHessian δ h).rank = 2) (Z : Fin 3 → F)
    (hY : (derivationHessian δ h) *ᵥ Y = 0)
    (a b : Fin 3) (hYa : Y a ≠ 0) (hZa : Z a = 0) (hZb : Z b = 1)
    (hZ : matrixBilinearPairing (derivationHessian δ h) Z Z = 0)
    (hCubic : (∑ i, ∑ j, ∑ k, derivationCubicTensor δ h i j k * Z i * Z j * Z k) = 0) :
    ∀ j : Fin 4, coordinateEuler Z δ (coordinateEuler Z δ ((Fin.snoc Y h : Fin 4 → F) j)) = 0 := by
  let D := coordinateEuler Z δ
  have hDZ (i : Fin 3) : D (Z i) = 0 :=
    congrFun (normalized_coordinate_hessian_direction_constant δ hcomm h hrank Y Z hY a b hYa hZa hZb hZ hCubic) i
  have hDY (i : Fin 3) : D (Y i) = Z i := by
    simp only [D, coordinateEuler_apply, hcoord]
    simp [apply_ite]
  have hD2h : D (D h) = 0 := by
    change D (∑ i, Z i * δ i h) = 0
    rw [map_sum]
    have he (i : Fin 3) : D (Z i * δ i h) = ∑ j, derivationHessian δ h i j * Z i * Z j := by
      rw [D.leibniz, hDZ, smul_zero, add_zero]
      change Z i * (∑ j, Z j * δ j (δ i h)) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      change Z i * (Z j * δ j (δ i h)) = δ i (δ j h) * Z i * Z j
      rw [hcomm j i]
      ring
    simp only [he]
    exact hZ
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · exact hD2h
  · simp only [Fin.snoc_castSucc]
    change D (D (Y i)) = 0
    rw [hDY, hDZ]

/-- Every ground-field equation of the graph point vanishes on its
entire tangent line in the normalized isotropic direction. -/
theorem normalized_hessian_direction_line_identity
    (δ : Fin 3 → Derivation K F F) (hcomm : ∀ i j a, δ i (δ j a) = δ j (δ i a))
    (Y : Fin 3 → F) (hcoord : ∀ i j, δ i (Y j) = if j = i then 1 else 0)
    (h : F) (hrank : (derivationHessian δ h).rank = 2) (Z : Fin 3 → F)
    (hY : (derivationHessian δ h) *ᵥ Y = 0)
    (a b : Fin 3) (hYa : Y a ≠ 0) (hZa : Z a = 0) (hZb : Z b = 1)
    (hZ : matrixBilinearPairing (derivationHessian δ h) Z Z = 0)
    (hCubic : (∑ i, ∑ j, ∑ k, derivationCubicTensor δ h i j k * Z i * Z j * Z k) = 0)
    (R : MvPolynomial (Fin 4) K) (hR : MvPolynomial.aeval (Fin.snoc Y h) R = 0) :
    MvPolynomial.aeval (fun j : Fin 4 => Polynomial.C (Fin.snoc Y h j) +
      Polynomial.C (Fin.snoc Z (∑ i, Z i * δ i h) j) * Polynomial.X) R = 0 := by
  have hacc := normalized_hessian_graph_zero_acceleration δ hcomm Y hcoord h hrank Z hY a b hYa hZa hZb hZ hCubic
  have hline := relation_vanishes_on_zero_acceleration_line (coordinateEuler Z δ) (Fin.snoc Y h) hacc R hR
  have hv : (fun j : Fin 4 => coordinateEuler Z δ ((Fin.snoc Y h : Fin 4 → F) j)) =
      Fin.snoc Z (∑ i, Z i * δ i h) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact coordinateEuler_apply Z δ h
    · simp only [Fin.snoc_castSucc]
      simp only [coordinateEuler_apply, hcoord]
      simp [apply_ite]
  have hfun : (fun j : Fin 4 => Polynomial.C ((Fin.snoc Y h : Fin 4 → F) j) +
      Polynomial.C (coordinateEuler Z δ ((Fin.snoc Y h : Fin 4 → F) j)) * Polynomial.X) =
      (fun j : Fin 4 => Polynomial.C ((Fin.snoc Y h : Fin 4 → F) j) +
        Polynomial.C ((Fin.snoc Z (∑ i, Z i * δ i h) : Fin 4 → F) j) * Polynomial.X) := by
    funext j
    exact congrArg (fun t : F => Polynomial.C ((Fin.snoc Y h : Fin 4 → F) j) +
      Polynomial.C t * Polynomial.X) (congrFun hv j)
  rw [hfun] at hline
  exact hline

end DimensionFourDependence
