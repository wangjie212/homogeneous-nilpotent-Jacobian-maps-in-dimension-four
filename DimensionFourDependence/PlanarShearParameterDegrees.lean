import DimensionFourDependence.PlanarInvariantAxisCoefficients
import DimensionFourDependence.PlanarInvariantCoefficientDescent

/-! # Exact homogeneous coefficient weights in equation (6.9) -/

namespace DimensionFourDependence.Shear

open MvPolynomial

set_option maxHeartbeats 1300000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "L" => FractionRing R₂
local notation "Aₗ" => MvPolynomial (Fin 2) L
local notation "ι" => (algebraMap R₂ L)

/-- The pure x coefficient of the original multiplier is exactly
the corresponding power of a times the base parameter coefficient. -/
theorem planar_shear_parameter_pure_active_coefficient
    (a b : R₂) (q : R₄) (f : Polynomial R₂)
    (hf : activeFractionPolynomial q =
      Polynomial.aeval (C (ι a) * X 0 + C (ι b) * X 1 : Aₗ) (f.map ι)) (j : ℕ) :
    (planarCoefficientEquiv q).coeff (Finsupp.single 0 j) = a ^ j * f.coeff j := by
  let s : Fin 2 → Polynomial R₂ := ![Polynomial.X, 0]
  let S : Aₗ := C (ι a) * X 0 + C (ι b) * X 1
  have hs : aeval (fun i => (s i).map ι) S = Polynomial.C (ι a) * Polynomial.X := by
    simp [s, S]
  have he := invariant_parameter_coeff_mul_is_base_on_axis S (planarCoefficientEquiv q) (f.map ι)
    hf s a hs j
  rw [show (aeval s (planarCoefficientEquiv q)).coeff j = _ from
      active_first_axis_coefficient (planarCoefficientEquiv q) j, Polynomial.coeff_map, ← map_mul] at he
  exact (IsFractionRing.injective R₂ L) he

/-- Removing the active-origin translations removes exactly the constant
term of the univariate shear parameter. -/
theorem normalized_planar_shear_parameter_constant_zero
    (p q : R₄) (a b : R₂) (hb : b ≠ 0)
    (hp : planarActiveNormalized p = base4 b * q) (f : Polynomial R₂)
    (hf : activeFractionPolynomial q =
      Polynomial.aeval (C (ι a) * X 0 + C (ι b) * X 1 : Aₗ) (f.map ι)) : f.coeff 0 = 0 := by
  have hq := planarCoefficientEquiv_normalized_at_origin p
  rw [hp, map_mul, planarCoefficientEquiv_base4, map_mul, aeval_C] at hq
  have he := (mul_eq_zero.mp hq).resolve_left hb
  have hzero : (planarCoefficientEquiv q).coeff 0 = 0 := by
    simpa only [aeval_eq_eval, eval_zero', constantCoeff_eq] using he
  have h := planar_shear_parameter_pure_active_coefficient a b q f hf 0
  simpa [hzero] using h.symm

/-- The nonzero coefficient of S^j has degree `D-j(r+1)` when the
multiplier has degree D and the base coefficients have degree r. -/
theorem homogeneous_planar_shear_parameter_coeff_degree
    (q : R₄) {D r : ℕ} (hq : q.IsHomogeneous D) (qne : q ≠ 0)
    (a b : R₂) (ha : a.IsHomogeneous r) (hane : a ≠ 0)
    (f : Polynomial R₂) (hf : activeFractionPolynomial q =
      Polynomial.aeval (C (ι a) * X 0 + C (ι b) * X 1 : Aₗ) (f.map ι))
    (j : ℕ) (hj : f.coeff j ≠ 0) :
    j * (r + 1) ≤ D ∧ (f.coeff j).IsHomogeneous (D - j * (r + 1)) := by
  let m : Fin 2 →₀ ℕ := Finsupp.single 0 j
  have hm : m.degree = j := Finsupp.degree_single _ _
  have hcoef : (planarCoefficientEquiv q).coeff m = a ^ j * f.coeff j :=
    planar_shear_parameter_pure_active_coefficient a b q f hf j
  have hne : a ^ j * f.coeff j ≠ 0 := mul_ne_zero (pow_ne_zero _ hane) hj
  have hjD : j ≤ D := by
    by_contra! hh
    have hb : q.totalDegree < m.degree := by rw [hq.totalDegree qne, hm]; exact hh
    exact hne (hcoef.symm.trans (planarCoefficientEquiv_coeff_eq_zero_of_totalDegree_lt q m hb))
  have hprod := homogeneous_planarCoefficientEquiv_coeff q hq m
  rw [hcoef, hm] at hprod
  have hpow : (a ^ j).IsHomogeneous (j * r) := by
    simpa only [Nat.mul_comm r j] using ha.pow j
  have hdeg := hprod.totalDegree hne
  rw [totalDegree_mul_of_isDomain (pow_ne_zero _ hane) hj,
    hpow.totalDegree (pow_ne_zero _ hane)] at hdeg
  have hjr : j * r ≤ D - j := by omega
  have he : j * r + (D - j * (r + 1)) = D - j := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  refine ⟨by rw [Nat.mul_add, Nat.mul_one]; omega, ?_⟩
  exact homogeneous_factor_of_product (pow_ne_zero _ hane) hpow (he.symm ▸ hprod)

end DimensionFourDependence.Shear
