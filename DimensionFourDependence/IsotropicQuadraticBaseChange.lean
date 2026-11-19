import DimensionFourDependence.IsotropicQuadraticCoordinates

/-! # Isotropic coordinates over extensions of the coefficient field

The fiber coordinates and the isotropic directions may lie in extensions
of the coefficient field. The normal form is therefore proved after
arbitrary field extension, as required for geometric generic fibers.
-/

namespace DimensionFourDependence

variable {F A : Type*} [Field F] [Field A] [Algebra F A] {n : ℕ}

/-- A componentwise radial radical remains a radical after scalar extension. -/
theorem matrixBilinearPairing_radical_map
    (T : Matrix (Fin n) (Fin n) F) (Y : Fin n → F)
    (hY : ∀ j, ∑ i, Y i * T i j = 0) (v : Fin n → A) :
    matrixBilinearPairing (T.map (algebraMap F A)) (fun i => algebraMap F A (Y i)) v = 0 := by
  unfold matrixBilinearPairing
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  rw [← Finset.sum_mul]
  have he : (∑ i, algebraMap F A (T i j) * algebraMap F A (Y i)) = 0 := by
    simp only [← map_mul, ← map_sum]
    have hz : (∑ i, T i j * Y i) = 0 := by
      simpa only [mul_comm] using hY j
    rw [hz, map_zero]
  change (∑ i, algebraMap F A (T i j) * algebraMap F A (Y i)) * v j = 0
  rw [he, zero_mul]

/-- The isotropic quadratic normal form is valid after any field extension. -/
theorem quadraticExpression_radial_isotropic_base_change [CharZero A]
    (a : Fin n → F) (T : Matrix (Fin n) (Fin n) F) (hT : ∀ i j, T i j = T j i)
    (Y : Fin n → F) (hY : ∀ j, ∑ i, Y i * T i j = 0)
    (Z W : Fin n → A)
    (hZ : matrixBilinearPairing (T.map (algebraMap F A)) Z Z = 0)
    (hW : matrixBilinearPairing (T.map (algebraMap F A)) W W = 0)
    (θ c : F) (τ s t : A) (haY : ∑ i, a i * Y i = θ * c) :
    quadraticExpression (fun i => algebraMap F A (a i)) (T.map (algebraMap F A))
      (fun i => τ * algebraMap F A (Y i) + s * Z i + t * W i) =
      algebraMap F A θ * algebraMap F A c * τ +
        (∑ i, algebraMap F A (a i) * Z i) * s +
        (∑ i, algebraMap F A (a i) * W i) * t +
        matrixBilinearPairing (T.map (algebraMap F A)) Z W * s * t := by
  apply quadraticExpression_radial_isotropic_coordinates
    (fun i => algebraMap F A (a i)) (T.map (algebraMap F A))
    (fun i j => congrArg (algebraMap F A) (hT i j))
    (fun i => algebraMap F A (Y i)) Z W
    (matrixBilinearPairing_radical_map T Y hY) hZ hW
  simpa only [← map_mul, ← map_sum] using congrArg (algebraMap F A) haY

variable {K : Type*} [Field K] [CharZero K]

/-- The actual equation (3.3) coefficient expansion allows both fiber
parameters and isotropic directions in an arbitrary extension of `L`. -/
theorem coefficient_quadratic_radial_isotropic_coordinates_over
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c : coefficientField (K := K) Y) (θ : K)
    (hh : coefficientEuler Y hY h = h)
    (hc : coefficientEuler Y hY c = algebraMap K (coefficientField (K := K) Y) θ * c)
    (G : Type*) [Field G] [CharZero G] [Algebra (coefficientField (K := K) Y) G]
    (Z W : Fin 3 → G)
    (hZ : matrixBilinearPairing ((coefficientHessian Y hY h).map
      (algebraMap (coefficientField (K := K) Y) G)) Z Z = 0)
    (hW : matrixBilinearPairing ((coefficientHessian Y hY h).map
      (algebraMap (coefficientField (K := K) Y) G)) W W = 0)
    (τ s t : G) :
    let L := coefficientField (K := K) Y
    quadraticExpression (fun i => algebraMap L G (coefficientGradient Y hY c i))
      ((coefficientHessian Y hY h).map (algebraMap L G))
      (fun i => τ * algebraMap L G (coefficientCoordinate (K := K) Y i) + s * Z i + t * W i) =
      algebraMap L G (algebraMap K L θ) * algebraMap L G c * τ +
        (∑ i, algebraMap L G (coefficientGradient Y hY c i) * Z i) * s +
        (∑ i, algebraMap L G (coefficientGradient Y hY c i) * W i) * t +
        matrixBilinearPairing ((coefficientHessian Y hY h).map (algebraMap L G)) Z W * s * t := by
  apply quadraticExpression_radial_isotropic_base_change
    (coefficientGradient Y hY c) (coefficientHessian Y hY h)
    (coefficientHessian_symmetric Y hY h) (coefficientCoordinate (K := K) Y)
    (coefficientHessian_radial_contraction Y hY h hh) Z W hZ hW
  calc
    (∑ i, coefficientGradient Y hY c i * coefficientCoordinate (K := K) Y i) =
        ∑ i, coefficientCoordinate (K := K) Y i * coefficientPartial Y hY i c :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    _ = coefficientEuler Y hY c := (coefficientEuler_apply Y hY c).symm
    _ = algebraMap K (coefficientField (K := K) Y) θ * c := hc

end DimensionFourDependence
