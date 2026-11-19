import DimensionFourDependence.LinearProjectionCoordinateChange

/-! # Original projective coordinate integrality from the actual projection

The inverse coordinate change recovers each original coordinate as a
linear combination of the actual projection coordinates. This identity
also holds after scaling by a frame parameter. The actual original
homogeneous linear form supplies the new frame and its four coordinate
ratios, without changing the original projective chart system.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k L : Type*} [Field k] [Field L] [Algebra k L] {n : ℕ}

/-- The new coordinates are the actual inverse-matrix linear forms in
the original affine coordinates, including over coefficient extensions. -/
theorem linearProjectionCoordinate_eq_sum
    (T : (Fin n → k) ≃ₗ[k] (Fin n → k)) (x : Fin n → L) (i : Fin n) :
    linearProjectionCoordinate T x i =
      ∑ j, algebraMap k L (LinearMap.toMatrix' T.symm.toLinearMap i j) * x j := by
  change aeval x (aeval (linearPolynomialMap (LinearMap.toMatrix' T.symm.toLinearMap)) (X i)) = _
  simp only [aeval_X, linearPolynomialMap, map_sum, map_mul, aeval_C]

/-- Every original affine coordinate is the actual forward-matrix
linear combination of the constructed projection coordinate values. -/
theorem original_coordinate_eq_projection_sum
    (T : (Fin n → k) ≃ₗ[k] (Fin n → k)) (x : Fin n → L) (i : Fin n) :
    x i = ∑ j, algebraMap k L (LinearMap.toMatrix' T.toLinearMap i j) *
      linearProjectionCoordinate T x j := by
  have h := linearProjectionCoordinate_eval_transformed T x (X i)
  simpa only [linearPolynomialPullback, aeval_X, linearPolynomialMap,
    map_sum, map_mul, aeval_C] using h.symm

variable {R : Type*} [CommRing R] [Algebra R L]

/-- Integrality of the scaled projection coordinates and original
constants implies integrality of all scaled original coordinates. -/
theorem original_scaled_coordinates_integral_of_projection
    (T : (Fin n → k) ≃ₗ[k] (Fin n → k)) (x : Fin n → L) (t : L)
    (hconstants : ∀ a : k, IsIntegral R (algebraMap k L a))
    (hnew : ∀ j, IsIntegral R (t * linearProjectionCoordinate T x j)) :
    ∀ i, IsIntegral R (t * x i) := by
  intro i
  rw [original_coordinate_eq_projection_sum T x i, Finset.mul_sum]
  have hsum : (∑ j, t * (algebraMap k L (LinearMap.toMatrix' T.toLinearMap i j) *
      linearProjectionCoordinate T x j)) =
      ∑ j, algebraMap k L (LinearMap.toMatrix' T.toLinearMap i j) *
        (t * linearProjectionCoordinate T x j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  exact IsIntegral.sum _ (fun j _ => (hconstants _).mul (hnew j))

/-- Coefficients of the original homogeneous linear form corresponding
to a specified new affine projection coordinate. -/
noncomputable def projectionProjectiveFrameCoefficients
    (T : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k))
    (s : Fin 4 ≃ Option (Fin 3)) (j : Fin 3) : Fin 4 → k :=
  fun i => (s i).elim 0 (fun l => LinearMap.toMatrix' T.symm.toLinearMap j l)

/-- The constructed new affine coordinate is the ratio of its actual
original homogeneous linear form by the old frame coordinate. -/
theorem projection_projective_frame_eq
    (T : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k)) (x : Fin 4 → L)
    (s : Fin 4 ≃ Option (Fin 3)) (hbase : x (s.symm none) ≠ 0) (j : Fin 3) :
    (∑ i, algebraMap k L (projectionProjectiveFrameCoefficients T s j i) * x i) =
      x (s.symm none) * linearProjectionCoordinate T
        (fun l => x (s.symm (some l)) / x (s.symm none)) j := by
  classical
  have hsum : (∑ i, algebraMap k L (projectionProjectiveFrameCoefficients T s j i) * x i) =
      ∑ l : Fin 3, algebraMap k L (LinearMap.toMatrix' T.symm.toLinearMap j l) *
        x (s.symm (some l)) := by
    rw [← s.symm.sum_comp (fun i => algebraMap k L (projectionProjectiveFrameCoefficients T s j i) * x i)]
    simp [projectionProjectiveFrameCoefficients]
  rw [hsum, linearProjectionCoordinate_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  field_simp

/-- If the old frame ratio and all actual scaled projection coordinates
are integral, every original homogeneous-coordinate ratio in the new
frame is integral over the same base. -/
theorem projective_ratios_integral_of_scaled_projection
    (T : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k)) (x : Fin 4 → L)
    (s : Fin 4 ≃ Option (Fin 3)) (hbase : x (s.symm none) ≠ 0)
    (h : L) (hh : h ≠ 0)
    (hconstants : ∀ a : k, IsIntegral R (algebraMap k L a))
    (ht : IsIntegral R (x (s.symm none) / h))
    (hnew : ∀ j, IsIntegral R ((x (s.symm none) / h) * linearProjectionCoordinate T
      (fun l => x (s.symm (some l)) / x (s.symm none)) j)) :
    ∀ i, IsIntegral R (x i / h) := by
  have hscaled := original_scaled_coordinates_integral_of_projection T
    (fun l => x (s.symm (some l)) / x (s.symm none)) (x (s.symm none) / h) hconstants hnew
  intro i
  cases hsi : s i with
  | none =>
    have hi : i = s.symm none := by rw [← hsi, s.symm_apply_apply]
    rw [hi]
    exact ht
  | some j =>
    have hi : i = s.symm (some j) := by rw [← hsi, s.symm_apply_apply]
    have heq : (x (s.symm none) / h) * (x (s.symm (some j)) / x (s.symm none)) = x i / h := by
      rw [hi]
      field_simp
    exact Eq.mp (congrArg (fun z : L => IsIntegral R z) heq) (hscaled j)

end DimensionFourDependence
