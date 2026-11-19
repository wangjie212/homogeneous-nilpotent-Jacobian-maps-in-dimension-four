import DimensionFourDependence.AlgebraicPolynomialDescent
import DimensionFourDependence.PrimitiveRationalVector

/-! # Descent from an actual independent-parameter field identity

Evaluation at a parameter transcendental over the source-coordinate
field is injective. Algebraicity of its value over the parameter field
therefore reflects to algebraicity of the whole polynomial over the
original polynomial ring. A scaled-power identity with an algebraic
parameter coefficient constructs projective polynomial descent.
-/

namespace DimensionFourDependence

open Polynomial

attribute [local instance] Polynomial.algebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K F L : Type*} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]

/-- Algebraicity at a parameter independent of the source-coordinate
field reflects to algebraicity of the whole coefficient polynomial. -/
theorem independent_parameter_algebraicity_reflects_to_polynomial
    (t : L) (ht : Transcendental F t) (P : Polynomial F)
    (halg : letI : Algebra (Polynomial K) L := (Polynomial.aeval (R := K) t).toRingHom.toAlgebra
      IsAlgebraic (Polynomial K) (Polynomial.aeval t P)) :
    IsAlgebraic (Polynomial K) P := by
  let : Algebra (Polynomial K) L := (Polynomial.aeval (R := K) t).toRingHom.toAlgebra
  let ψ : Polynomial F →ₐ[Polynomial K] L :=
    { (Polynomial.aeval (R := F) t).toRingHom with
      commutes' := by
        intro Q
        change Polynomial.aeval (R := F) t (Q.map (algebraMap K F)) =
          Polynomial.aeval (R := K) t Q
        simp only [Polynomial.aeval_def, Polynomial.eval₂_map,
          ← IsScalarTower.algebraMap_eq K F L] }
  apply (isAlgebraic_algHom_iff ψ (transcendental_iff_injective.mp ht)).mp
  exact halg

variable [IsAlgClosed K]

/-- An actual scaled-power identity with an algebraic parameter
coefficient forces the original polynomial pairing to descend up to
its actual leading coefficient. -/
theorem independent_parameter_scaled_power_constructs_projective_polynomial
    (φ : RatFunc K →ₐ[K] L) (t : L) (hφ : φ RatFunc.X = t)
    (ht : Transcendental F t) (P : Polynomial F) (hP : P ≠ 0)
    (h : F) (hh : h ≠ 0) (d : ℕ) (hd : 0 < d) (k : L)
    (hk : letI : Algebra (RatFunc K) L := φ.toRingHom.toAlgebra
      IsAlgebraic (RatFunc K) k)
    (hvalue : (Polynomial.aeval t P) ^ d = k * algebraMap F L h) :
    ∃ P₀ : Polynomial K, P = C P.leadingCoeff * P₀.map (algebraMap K F) := by
  let : Algebra (RatFunc K) L := φ.toRingHom.toAlgebra
  let : Algebra (Polynomial K) L := (Polynomial.aeval (R := K) t).toRingHom.toAlgebra
  let : IsScalarTower (Polynomial K) (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq (fun Q => by
      change Polynomial.aeval (R := K) t Q = φ (algebraMap (Polynomial K) (RatFunc K) Q)
      rw [rational_function_algHom_polynomial_value, hφ])
  let : Algebra.IsAlgebraic (Polynomial K) (RatFunc K) :=
    IsLocalization.isAlgebraic (RatFunc K) (nonZeroDivisors (Polynomial K))
  let Z : Polynomial F := C h⁻¹ * P ^ d
  have hZ : Polynomial.aeval t Z = k := by
    dsimp only [Z]
    rw [map_mul, map_pow, Polynomial.aeval_C, hvalue, map_inv₀]
    have hhL : algebraMap F L h ≠ 0 := (_root_.map_ne_zero _).mpr hh
    field_simp
  have hZalg : IsAlgebraic (Polynomial K) (Polynomial.aeval t Z) := by
    rw [hZ]
    exact hk.restrictScalars (Polynomial K)
  have hpoly := independent_parameter_algebraicity_reflects_to_polynomial t ht Z hZalg
  exact algebraic_scaled_power_constructs_projective_polynomial_descent P hP h hh d hd hpoly

end DimensionFourDependence
