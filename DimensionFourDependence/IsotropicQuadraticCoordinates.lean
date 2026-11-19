import DimensionFourDependence.WeightedFiberInvariants

/-! # The quadratic equation in radial and isotropic coordinates

The algebraic expansion gives (3.3) once two isotropic directions are
chosen. Existence of the directions and the later pole argument are separate.
-/

namespace DimensionFourDependence

variable {F : Type*} [Field F] {n : ℕ}

/-- Bilinear contraction of a coefficient matrix with two vectors. -/
noncomputable def matrixBilinearPairing (T : Matrix (Fin n) (Fin n) F) (x y : Fin n → F) : F :=
  ∑ i, ∑ j, T i j * x i * y j

theorem matrixBilinearPairing_add_left (T : Matrix (Fin n) (Fin n) F) (x x' y : Fin n → F) :
    matrixBilinearPairing T (fun i => x i + x' i) y =
      matrixBilinearPairing T x y + matrixBilinearPairing T x' y := by
  simp only [matrixBilinearPairing, mul_add, add_mul, Finset.sum_add_distrib]

theorem matrixBilinearPairing_add_right (T : Matrix (Fin n) (Fin n) F) (x y y' : Fin n → F) :
    matrixBilinearPairing T x (fun i => y i + y' i) =
      matrixBilinearPairing T x y + matrixBilinearPairing T x y' := by
  simp only [matrixBilinearPairing, mul_add, Finset.sum_add_distrib]

theorem matrixBilinearPairing_scale_left (T : Matrix (Fin n) (Fin n) F)
    (x y : Fin n → F) (r : F) :
    matrixBilinearPairing T (fun i => r * x i) y = r * matrixBilinearPairing T x y := by
  simp only [matrixBilinearPairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem matrixBilinearPairing_scale_right (T : Matrix (Fin n) (Fin n) F)
    (x y : Fin n → F) (r : F) :
    matrixBilinearPairing T x (fun i => r * y i) = r * matrixBilinearPairing T x y := by
  simp only [matrixBilinearPairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem matrixBilinearPairing_symmetric (T : Matrix (Fin n) (Fin n) F)
    (hT : ∀ i j, T i j = T j i) (x y : Fin n → F) :
    matrixBilinearPairing T x y = matrixBilinearPairing T y x := by
  unfold matrixBilinearPairing
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hT j i]
  ring

/-- A symmetric form with radial radical and two isotropic directions
has only the mixed isotropic term in these coordinates. -/
theorem quadratic_form_radial_isotropic_coordinates
    (T : Matrix (Fin n) (Fin n) F) (hT : ∀ i j, T i j = T j i)
    (Y Z W : Fin n → F) (hY : ∀ v, matrixBilinearPairing T Y v = 0)
    (hZ : matrixBilinearPairing T Z Z = 0) (hW : matrixBilinearPairing T W W = 0)
    (τ s t : F) :
    matrixBilinearPairing T (fun i => τ * Y i + s * Z i + t * W i)
      (fun i => τ * Y i + s * Z i + t * W i) =
        2 * matrixBilinearPairing T Z W * s * t := by
  have hZY : matrixBilinearPairing T Z Y = 0 :=
    (matrixBilinearPairing_symmetric T hT Z Y).trans (hY Z)
  have hWY : matrixBilinearPairing T W Y = 0 :=
    (matrixBilinearPairing_symmetric T hT W Y).trans (hY W)
  have hWZ := matrixBilinearPairing_symmetric T hT W Z
  simp only [matrixBilinearPairing_add_left, matrixBilinearPairing_add_right,
    matrixBilinearPairing_scale_left, matrixBilinearPairing_scale_right,
    hY, hZY, hWY, hZ, hW, hWZ]
  ring

/-- Equation (3.3): the weighted radial linear term and the mixed
isotropic term give the entire quadratic expression. -/
theorem quadraticExpression_radial_isotropic_coordinates [CharZero F]
    (a : Fin n → F) (T : Matrix (Fin n) (Fin n) F) (hT : ∀ i j, T i j = T j i)
    (Y Z W : Fin n → F) (hY : ∀ v, matrixBilinearPairing T Y v = 0)
    (hZ : matrixBilinearPairing T Z Z = 0) (hW : matrixBilinearPairing T W W = 0)
    (θ c τ s t : F) (haY : ∑ i, a i * Y i = θ * c) :
    quadraticExpression a T (fun i => τ * Y i + s * Z i + t * W i) =
      θ * c * τ + (∑ i, a i * Z i) * s + (∑ i, a i * W i) * t +
        matrixBilinearPairing T Z W * s * t := by
  have hlin : (∑ i, a i * (τ * Y i + s * Z i + t * W i)) =
      θ * c * τ + (∑ i, a i * Z i) * s + (∑ i, a i * W i) * t := by
    have he (i : Fin n) : a i * (τ * Y i + s * Z i + t * W i) =
        a i * Y i * τ + a i * Z i * s + a i * W i * t := by ring
    simp only [he, Finset.sum_add_distrib, ← Finset.sum_mul, haY]
  change (∑ i, a i * (τ * Y i + s * Z i + t * W i)) + (2 : F)⁻¹ *
    matrixBilinearPairing T (fun i => τ * Y i + s * Z i + t * W i)
      (fun i => τ * Y i + s * Z i + t * W i) = _
  rw [hlin, quadratic_form_radial_isotropic_coordinates T hT Y Z W hY hZ hW]
  have h2 : (2 : F) ≠ 0 := by norm_num
  field_simp [h2]

variable {K : Type*} [Field K] [CharZero K]

/-- Specialize (3.3) to the actual coefficient gradient and Hessian.
The radial radical and radial linear coefficient follow from Euler weights. -/
theorem coefficient_quadratic_radial_isotropic_coordinates
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c : coefficientField (K := K) Y) (θ : K)
    (hh : coefficientEuler Y hY h = h)
    (hc : coefficientEuler Y hY c = algebraMap K (coefficientField (K := K) Y) θ * c)
    (Z W : Fin 3 → coefficientField (K := K) Y)
    (hZ : matrixBilinearPairing (coefficientHessian Y hY h) Z Z = 0)
    (hW : matrixBilinearPairing (coefficientHessian Y hY h) W W = 0)
    (τ s t : coefficientField (K := K) Y) :
    quadraticExpression (coefficientGradient Y hY c) (coefficientHessian Y hY h)
      (fun i => τ * coefficientCoordinate (K := K) Y i + s * Z i + t * W i) =
      algebraMap K (coefficientField (K := K) Y) θ * c * τ +
        (∑ i, coefficientGradient Y hY c i * Z i) * s +
        (∑ i, coefficientGradient Y hY c i * W i) * t +
        matrixBilinearPairing (coefficientHessian Y hY h) Z W * s * t := by
  apply quadraticExpression_radial_isotropic_coordinates
    (coefficientGradient Y hY c) (coefficientHessian Y hY h)
    (coefficientHessian_symmetric Y hY h) (coefficientCoordinate (K := K) Y) Z W
    (fun v => coefficientHessian_radial_pairing Y hY h hh v) hZ hW
  calc
    (∑ i, coefficientGradient Y hY c i * coefficientCoordinate (K := K) Y i) =
        ∑ i, coefficientCoordinate (K := K) Y i * coefficientPartial Y hY i c :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    _ = coefficientEuler Y hY c := (coefficientEuler_apply Y hY c).symm
    _ = algebraMap K (coefficientField (K := K) Y) θ * c := hc

end DimensionFourDependence
