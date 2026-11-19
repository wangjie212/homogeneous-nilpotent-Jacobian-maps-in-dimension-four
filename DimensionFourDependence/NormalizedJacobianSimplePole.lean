import DimensionFourDependence.SimplePoleNilpotentObstruction
import DimensionFourDependence.Defs

/-! # The actual polynomial Jacobian has the simple-pole normal form

For `H = R^m a P`, the unit remainder `a` gives an integral logarithmic
derivative. The normalized Jacobian is the local matrix from Lemma 4.3,
and nilpotence of the original polynomial Jacobian survives normalization.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K F : Type*} [Field K] [Field F] {n : ℕ}

/-- The logarithmic derivative of the original polynomial factorization,
including multiplicity zero. -/
theorem polynomial_power_unit_logarithmic_derivative
    (f : MvPolynomial (Fin n) K →+* F)
    (R a : MvPolynomial (Fin n) K) (m : ℕ) (j : Fin n)
    (hR : f R ≠ 0) (ha : f a ≠ 0) :
    f (pderiv j (R ^ m * a)) / f (R ^ m * a) =
      (m : F) * f (pderiv j R) / f R + f (pderiv j a) / f a := by
  cases m with
  | zero => simp
  | succ m =>
    simp only [pderiv_mul, pderiv_pow, Nat.add_sub_cancel, map_add, map_mul,
      map_pow, map_natCast]
    field_simp
    ring

/-- Entrywise product differentiation gives the normalized Jacobian of
the actual polynomial map; no matrix decomposition is supplied. -/
theorem polynomial_factor_normalized_jacobian_entry
    (f : MvPolynomial (Fin n) K →+* F)
    (R a : MvPolynomial (Fin n) K) (m : ℕ)
    (P : Fin n → MvPolynomial (Fin n) K) (i j : Fin n)
    (hR : f R ≠ 0) (ha : f a ≠ 0) :
    (f (R ^ m * a))⁻¹ * f (jac (fun k => R ^ m * a * P k) i j) =
      f (jac P i j) + f (P i) *
        ((m : F) * f (pderiv j R) / f R + f (pderiv j a) / f a) := by
  have hg : f (R ^ m * a) ≠ 0 := by simpa only [map_mul, map_pow] using mul_ne_zero (pow_ne_zero m hR) ha
  change _ * f (pderiv j (R ^ m * a * P i)) = f (pderiv j (P i)) + _
  rw [pderiv_mul]
  have hlog := polynomial_power_unit_logarithmic_derivative f R a m j hR ha
  simp only [map_add, map_mul, map_pow] at hlog ⊢
  rw [← hlog]
  field_simp
  ring

variable {O : Type*} [CommRing O]
  [Algebra (MvPolynomial (Fin n) K) O] [Algebra (MvPolynomial (Fin n) K) F]
  [Algebra O F] [IsScalarTower (MvPolynomial (Fin n) K) O F]

/-- The regular part of the logarithmic derivative is integral because
the actual remainder is represented by a unit of the source local ring. -/
theorem localized_unit_logarithmic_gradient
    (a : MvPolynomial (Fin n) K) (u : Oˣ)
    (hu : algebraMap (MvPolynomial (Fin n) K) O a = (u : O)) (j : Fin n) :
    algebraMap O F (algebraMap (MvPolynomial (Fin n) K) O (pderiv j a) * (↑u⁻¹ : O)) =
      algebraMap (MvPolynomial (Fin n) K) F (pderiv j a) /
        algebraMap (MvPolynomial (Fin n) K) F a := by
  have he (x : MvPolynomial (Fin n) K) :
      algebraMap O F (algebraMap (MvPolynomial (Fin n) K) O x) =
        algebraMap (MvPolynomial (Fin n) K) F x :=
    (IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) K) O F x).symm
  have hui : algebraMap O F (↑u⁻¹ : O) = (algebraMap (MvPolynomial (Fin n) K) F a)⁻¹ := by
    rw [← he, hu]
    exact map_units_inv (algebraMap O F) u
  rw [map_mul, he, hui, div_eq_mul_inv]

/-- The paper's simple-pole matrix is derived from the original
polynomial factorization and the actual local unit remainder. -/
theorem normalized_jacobian_eq_simplePoleMatrix
    (R a : MvPolynomial (Fin n) K) (m : ℕ)
    (P : Fin n → MvPolynomial (Fin n) K) (u : Oˣ)
    (hu : algebraMap (MvPolynomial (Fin n) K) O a = (u : O))
    (hR : algebraMap (MvPolynomial (Fin n) K) F R ≠ 0) :
    (algebraMap (MvPolynomial (Fin n) K) F (R ^ m * a))⁻¹ •
        (jac (fun k => R ^ m * a * P k)).map (algebraMap (MvPolynomial (Fin n) K) F) =
      simplePoleMatrix F (algebraMap (MvPolynomial (Fin n) K) O R) (m : O)
        ((jac P).map (algebraMap (MvPolynomial (Fin n) K) O))
        (fun i => algebraMap (MvPolynomial (Fin n) K) O (P i))
        (fun j => algebraMap (MvPolynomial (Fin n) K) O (pderiv j R))
        (fun j => algebraMap (MvPolynomial (Fin n) K) O (pderiv j a) * (↑u⁻¹ : O)) := by
  have he (x : MvPolynomial (Fin n) K) :
      algebraMap O F (algebraMap (MvPolynomial (Fin n) K) O x) =
        algebraMap (MvPolynomial (Fin n) K) F x :=
    (IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) K) O F x).symm
  have ha : algebraMap (MvPolynomial (Fin n) K) F a ≠ 0 := by
    rw [← he, hu]
    exact (u.isUnit.map (algebraMap O F)).ne_zero
  ext i j
  change _ * algebraMap (MvPolynomial (Fin n) K) F (jac _ i j) = _
  rw [polynomial_factor_normalized_jacobian_entry _ R a m P i j hR ha]
  simp only [simplePoleMatrix, Matrix.map_apply, he, map_natCast,
    localized_unit_logarithmic_gradient a u hu]

/-- The local simple-pole matrix is nilpotent whenever the actual
polynomial Jacobian is nilpotent. -/
theorem simplePoleMatrix_isNilpotent_of_polynomial_jacobian
    (R a : MvPolynomial (Fin n) K) (m : ℕ)
    (P : Fin n → MvPolynomial (Fin n) K) (u : Oˣ)
    (hu : algebraMap (MvPolynomial (Fin n) K) O a = (u : O))
    (hR : algebraMap (MvPolynomial (Fin n) K) F R ≠ 0)
    (hN : IsNilpotent (jac (fun k => R ^ m * a * P k))) :
    IsNilpotent (simplePoleMatrix F (algebraMap (MvPolynomial (Fin n) K) O R) (m : O)
      ((jac P).map (algebraMap (MvPolynomial (Fin n) K) O))
      (fun i => algebraMap (MvPolynomial (Fin n) K) O (P i))
      (fun j => algebraMap (MvPolynomial (Fin n) K) O (pderiv j R))
      (fun j => algebraMap (MvPolynomial (Fin n) K) O (pderiv j a) * (↑u⁻¹ : O))) := by
  rw [← normalized_jacobian_eq_simplePoleMatrix R a m P u hu hR]
  exact (hN.map (algebraMap (MvPolynomial (Fin n) K) F).mapMatrix).smul _

end DimensionFourDependence
