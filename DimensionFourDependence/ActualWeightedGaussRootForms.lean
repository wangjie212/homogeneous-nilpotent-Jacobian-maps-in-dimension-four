import DimensionFourDependence.ParametricLinearRootForms
import DimensionFourDependence.ExtendedCoefficientEuler
import DimensionFourDependence.OriginalMapFiniteGaussBoundary

/-! # The actual invariant product nc has the finite linear-root data (4.4)

The original graph parameter and invariant supply the actual Euler
weights. Their algebraic coefficient extension is a surface over the
parameter image. A nonzero algebraic ruling direction with zero
acceleration therefore constructs finite coefficient fields and all
three original covectors n,m,s, with the rational root formula retained.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hGauss : gaussImageDimension H I = 1) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh e
local notation "A₀" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "n₀" => parametricRulingDenominator (f₀) (A₀) (coefficientCoordinate (K := K) (Y))

variable (κ : Type u) [Field κ]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) κ]
    [Algebra K κ]
    [IsScalarTower K (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) κ]
    [Algebra.IsAlgebraic (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) κ]

local notation "g" => IsScalarTower.toAlgHom K (L) κ
local notation "f" => (g).comp (f₀)
local notation "y" => fun i => (g) (coefficientCoordinate (K := K) (Y) i)
local notation "δ" => extendedCoefficientPartial (Y) hY κ
local notation "J" => (f).fieldRange

include hh hGauss hd hH

/-- The actual original invariant product nc gives finite linear-root
forms over its actual parameter image. No binary function field,
longitudinal coordinate, transverse coordinate or factorization is assumed. -/
theorem actual_gauss_invariant_product_finite_linear_root_forms
    (c : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h) (hc0 : c ≠ 0)
    (v : Fin 3 → κ) (hv0 : v ≠ 0)
    (hv : (fun i => (f) (rationalParameterDerivative K ((A₀) i))) ⬝ᵥ v = 0)
    (halg : ∀ i, IsAlgebraic (J) (v i))
    (hsecond : coordinateEuler v (δ) (coordinateEuler v (δ) ((g) ((n₀) * c))) = 0) :
    ∃ C : IntermediateField (J) κ, Module.Finite (J) C ∧
      ∃ (m s : Fin 3 → C) (ρ : κ), m ≠ 0 ∧ s ≠ 0 ∧ ρ ≠ 0 ∧
        (g) ((n₀) * c) = ((fun i => (m i : κ)) ⬝ᵥ (y)) * ρ ∧
        ρ ^ d = (fun i => (s i : κ)) ⬝ᵥ (y) ∧ (fun i => (s i : κ)) ⬝ᵥ v = 0 ∧
        coordinateEuler v (δ) ρ = 0 := by
  have hcoord : ∀ i j, (δ) i ((y) j) = if j = i then 1 else 0 :=
    extendedCoefficientPartial_coordinate (Y) hY κ
  have htangent : (fun i => (f) (rationalParameterDerivative K ((A₀) i))) ⬝ᵥ (y) = 0 := by
    simpa only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, dotProduct, map_sum, map_mul, map_zero] using
      congrArg (g) (actual_closed_gauss_graph_ruling_equation H I p hY h hh e hd hH)
  have hfirst : (fun i => (f) (rationalParameterDerivative K ((A₀) i))) ≠ 0 := by
    intro hz
    apply actual_closed_gauss_graph_gradient_derivative_ne_zero H I p hY h hh e hGauss
    funext i
    apply (g).injective
    change (g) ((f₀) (rationalParameterDerivative K ((A₀) i))) = (g) 0
    rw [map_zero]
    change (f) (rationalParameterDerivative K ((A₀) i)) = 0
    exact congrFun hz i
  have htD : coordinateEuler v (δ) ((f) RatFunc.X) = 0 :=
    parametric_ruling_direction_fixes_parameter (f) (δ) (y) hcoord (A₀) htangent hfirst v hv
  have htE : coordinateEuler (y) (δ) ((f) RatFunc.X) = 0 := by
    change coordinateEuler
      (fun i => algebraMap (L) κ (coefficientCoordinate (K := K) (Y) i)) (δ)
      (algebraMap (L) κ ((f₀) RatFunc.X)) = 0
    rw [extendedCoefficientEuler_extends,
      actual_closed_gauss_graph_parameter_output_euler_zero H I p hY h hh e hd hH, map_zero]
  have hweight : coordinateEuler (y) (δ) ((g) ((n₀) * c)) =
      (1 + (d : κ)⁻¹) * (g) ((n₀) * c) := by
    change coordinateEuler
      (fun i => algebraMap (L) κ (coefficientCoordinate (K := K) (Y) i)) (δ)
      (algebraMap (L) κ ((n₀) * c)) = _
    rw [extendedCoefficientEuler_extends,
      actual_closed_gauss_first_invariant_product_output_weight H I p hY h hh e hd hH c hc]
    simp only [map_mul, map_add, map_one, map_inv₀, map_natCast]
    rfl
  have hf : (g) ((n₀) * c) ≠ 0 := (map_ne_zero (g)).mpr
    (mul_ne_zero (actual_closed_gauss_graph_denominator_ne_zero H I p hY h hh e hGauss hd hH) hc0)
  exact parametric_weighted_function_finite_linear_root_forms (f) (δ) (y) v hcoord
    (extendedCoefficientPartials_commute (Y) hY κ) hv0 halg htD htE
    (algebraic_coefficient_extension_absolute_trdeg (Y) hY κ).le hd ((g) ((n₀) * c)) hf hsecond hweight

/-- The actual denominator covector is retained with the finite
linear-root forms (4.4), including the rational formula rho=n(Y)c/m(Y).
Every coefficient is in the same constructed finite parameter extension. -/
theorem actual_gauss_invariant_product_finite_three_root_forms
    (c : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h) (hc0 : c ≠ 0)
    (v : Fin 3 → κ) (hv0 : v ≠ 0)
    (hv : (fun i => (f) (rationalParameterDerivative K ((A₀) i))) ⬝ᵥ v = 0)
    (halg : ∀ i, IsAlgebraic (J) (v i))
    (hsecond : coordinateEuler v (δ) (coordinateEuler v (δ) ((g) ((n₀) * c))) = 0) :
    ∃ C : IntermediateField (J) κ, Module.Finite (J) C ∧
      ∃ (n m s : Fin 3 → C) (ρ : κ), n ≠ 0 ∧ m ≠ 0 ∧ s ≠ 0 ∧ ρ ≠ 0 ∧
        ((fun i => (n i : κ)) ⬝ᵥ (y)) = (g) (n₀) ∧
        ((fun i => (n i : κ)) ⬝ᵥ (y)) * (g) c = ((fun i => (m i : κ)) ⬝ᵥ (y)) * ρ ∧
        ρ ^ d = (fun i => (s i : κ)) ⬝ᵥ (y) ∧ (fun i => (s i : κ)) ⬝ᵥ v = 0 ∧
        coordinateEuler v (δ) ρ = 0 ∧
        ρ = (((fun i => (n i : κ)) ⬝ᵥ (y)) * (g) c) / ((fun i => (m i : κ)) ⬝ᵥ (y)) ∧
        (∀ i, n i = algebraMap (J) C
          ((f).equivFieldRange (rationalParameterDerivative K (rationalParameterDerivative K ((A₀) i))))) := by
  obtain ⟨C, hfin, m, s, ρ, hm, hs, hρ, hfactor, hroot, hsv, hρD⟩ :=
    actual_gauss_invariant_product_finite_linear_root_forms H I p hY h hh e hGauss hd hH κ c hc hc0 v hv0 hv halg hsecond
  let n : Fin 3 → C := fun i => algebraMap (J) C
    ((f).equivFieldRange (rationalParameterDerivative K (rationalParameterDerivative K ((A₀) i))))
  have hny : (fun i => (n i : κ)) ⬝ᵥ (y) = (g) (n₀) := by
    change (∑ i, (f) (rationalParameterDerivative K (rationalParameterDerivative K ((A₀) i))) * (y) i) =
      (g) (∑ i, (f₀) (rationalParameterDerivative K (rationalParameterDerivative K ((A₀) i))) *
        coefficientCoordinate (K := K) (Y) i)
    simp only [map_sum, map_mul, AlgHom.comp_apply]
  have hnvalue : (g) (n₀) ≠ 0 := (map_ne_zero (g)).mpr
    (actual_closed_gauss_graph_denominator_ne_zero H I p hY h hh e hGauss hd hH)
  have hn : n ≠ 0 := by
    intro hz
    have he := hny
    rw [hz] at he
    have hz' : (fun i => ((0 : Fin 3 → C) i : κ)) = 0 := by funext i; rfl
    rw [hz', zero_dotProduct] at he
    exact hnvalue he.symm
  have hmvalue : (fun i => (m i : κ)) ⬝ᵥ (y) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hfactor
    exact (mul_ne_zero hnvalue ((map_ne_zero (g)).mpr hc0)) (by simpa only [map_mul] using hfactor)
  have hprod : ((fun i => (n i : κ)) ⬝ᵥ (y)) * (g) c = ((fun i => (m i : κ)) ⬝ᵥ (y)) * ρ := by
    rw [hny, ← map_mul]
    exact hfactor
  refine ⟨C, hfin, n, m, s, ρ, hn, hm, hs, hρ, hny, hprod, hroot, hsv, hρD, ?_, fun _ => rfl⟩
  apply (eq_div_iff hmvalue).mpr
  exact (mul_comm _ _).trans hprod.symm

end DimensionFourDependence
