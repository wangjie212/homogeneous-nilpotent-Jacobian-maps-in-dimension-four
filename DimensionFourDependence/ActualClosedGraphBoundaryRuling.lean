import DimensionFourDependence.ActualSpecifiedSimpleRootBoundary

/-! # The actual full boundary lies on the same closed-parameter graph ruling -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

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

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "x" => rationalCoordinate (K := K) (n := 4)
local notation "x₃" => fun i : Fin 3 => (x) (p i.castSucc)
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh e
local notation "A₀" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "y₀" => coefficientCoordinate (K := K) (Y)
local notation "n₀" => parametricRulingDenominator (f₀) (A₀) (y₀)
local notation "Λ₀" => parametricGraphCubicCovector (f₀) (A₀) (y₀)

variable (F : Type u) [Field F]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) F]
    [Algebra K F]
    [IsScalarTower K (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) F]
    [Algebra.IsAlgebraic (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) F]

local notation "g" => IsScalarTower.toAlgHom K (L) F
local notation "f" => (g).comp (f₀)
local notation "y" => fun i => (g) ((y₀) i)
local notation "delta" => extendedCoefficientPartial (Y) hY F

/-- The original quadratic invariant puts each actual full boundary
point in the ruling defined by the same closed Gauss parameter. -/
theorem actual_full_boundary_closed_graph_ruling
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hGauss : gaussImageDimension H I = 1)
    (c q : L) (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (z : Option (Fin 4) → F) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (x))
    (hz0 : z none = 0) :
    (fun i => (f) (rationalParameterDerivative K ((A₀) i))) ⬝ᵥ
      (fun i : Fin 3 => z (some (p i.castSucc))) = 0 := by
  have hiso := projective_fiber_closure_quadratic_isotropic (x) z hz hpoint hz0
    (fun i : Fin 3 => p i.castSucc) (coefficientGradient (Y) hY c) (coefficientHessian (Y) hY h) q
    (quadraticFiberEquation_aeval_zero p (Y) hY h c q hq)
  have hB : (coefficientHessian (Y) hY h).map (algebraMap (L) F) =
      fun i j => -((f) (rationalParameterDerivative K ((A₀) i)) *
        (f) (rationalParameterDerivative K ((A₀) j))) / parametricRulingDenominator (f) (A₀) (y) := by
    rw [parametricRulingDenominator_map]
    ext i j
    rw [Matrix.map_apply, actual_closed_gauss_graph_hessian_formula H I p hY h hh e hGauss hd hH]
    simp only [map_div₀, map_neg, map_mul, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]
  rw [hB] at hiso
  have hdenom : parametricRulingDenominator (f) (A₀) (y) ≠ 0 := by
    rw [parametricRulingDenominator_map]
    exact (map_ne_zero (g)).mpr (actual_closed_gauss_graph_denominator_ne_zero H I p hY h hh e hGauss hd hH)
  exact (rank_one_quotient_isotropic_iff _ _ _ hdenom).mp hiso

end DimensionFourDependence
