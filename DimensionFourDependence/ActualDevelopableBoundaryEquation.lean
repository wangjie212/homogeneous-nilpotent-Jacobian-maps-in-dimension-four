import DimensionFourDependence.ActualDevelopableGraphEquations
import DimensionFourDependence.ParametricGraphBaseChange
import DimensionFourDependence.ExtendedCoefficientPartials

/-! # The actual developable boundary equations in (4.3)

The quadratic-cubic equations are the original invariant equations.
Their rank-one factor and ruling denominator come from the original map.
The fixed finite boundary branch itself remains a separate construction.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

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
local notation "y₀" => coefficientCoordinate (K := K) (Y)
local notation "n₀" => parametricRulingDenominator (f₀) (A₀) (y₀)
local notation "Λ₀" => parametricGraphCubicCovector (f₀) (A₀) (y₀)

include hh hGauss hd hH

/-- Every original normalized residue direction at infinity of the
actual fiber satisfies the modified quadratic equation in (4.3).
Neither a cubic factor nor a modified-quadric equation is supplied. -/
theorem actual_closed_gauss_modified_cubic_boundary_equation
    (c q k : L)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q)
    {O κ : Type u} [CommRing O] [Field κ]
    [Algebra (L) O] [Algebra (L) κ] [Algebra O S₀] [IsScalarTower (L) O S₀]
    (π : O →ₐ[L] κ) (hinj : Function.Injective (algebraMap O S₀))
    (s : S₀) (z : Option (Fin 3) → O)
    (hz0 : algebraMap O S₀ (z none) = s)
    (hz : ∀ i, algebraMap O S₀ (z (some i)) = s * rationalCoordinate (K := K) (p i.castSucc))
    (hres0 : π (z none) = 0) :
    matrixBilinearPairing ((coefficientHessian (Y) hY c).map (algebraMap (L) κ))
      (fun i => π (z (some i))) (fun i => π (z (some i))) -
      (2 / 3 : κ) * ((fun i => algebraMap (L) κ ((Λ₀) i)) ⬝ᵥ (fun i => π (z (some i)))) *
        ((fun i => algebraMap (L) κ (coefficientPartial (Y) hY i c)) ⬝ᵥ (fun i => π (z (some i)))) = 0 := by
  let : CharZero (L) := charZero_of_injective_algebraMap (algebraMap K (L)).injective
  exact modified_cubic_fiber_boundary_equation π hinj
    (fun i => rationalCoordinate (K := K) (p i.castSucc)) s z hz0 hz hres0
    (coefficientGradient (Y) hY c) (coefficientGradient (Y) hY q) (Λ₀)
    (coefficientHessian (Y) hY h) (coefficientHessian (Y) hY c)
    (coefficientCubicTensor (Y) hY h) q k
    (actual_closed_gauss_graph_cubic_polynomial_factorization H I p hY h hh e hGauss hd hH)
    (quadraticFiberEquation_aeval_zero p (Y) hY h c q hq)
    (cubicFiberEquation_aeval_zero p (Y) hY h c q k hk)

/-- The original quadratic fiber equation forces its actual boundary
direction into the actual Gauss ruling. No ruling-membership condition
or rank-one Hessian presentation is supplied. -/
theorem actual_closed_gauss_quadratic_boundary_mem_ruling
    (c q : L) (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    {O κ : Type u} [CommRing O] [Field κ]
    [Algebra (L) O] [Algebra (L) κ] [Algebra O S₀] [IsScalarTower (L) O S₀]
    (π : O →ₐ[L] κ) (hinj : Function.Injective (algebraMap O S₀))
    (s : S₀) (z : Option (Fin 3) → O)
    (hz0 : algebraMap O S₀ (z none) = s)
    (hz : ∀ i, algebraMap O S₀ (z (some i)) = s * rationalCoordinate (K := K) (p i.castSucc))
    (hres0 : π (z none) = 0) :
    (fun i => algebraMap (L) κ ((f₀) (rationalParameterDerivative K ((A₀) i)))) ⬝ᵥ
      (fun i => π (z (some i))) = 0 := by
  let : CharZero (L) := charZero_of_injective_algebraMap (algebraMap K (L)).injective
  have he := quadratic_fiber_residue_direction_isotropic π hinj
    (fun i => rationalCoordinate (K := K) (p i.castSucc)) s z hz0 hz hres0
    (coefficientGradient (Y) hY c) (coefficientHessian (Y) hY h) q
    (quadraticFiberEquation_aeval_zero p (Y) hY h c q hq)
  have hB : (coefficientHessian (Y) hY h).map (algebraMap (L) κ) = fun i j =>
      -(algebraMap (L) κ ((f₀) (rationalParameterDerivative K ((A₀) i))) *
        algebraMap (L) κ ((f₀) (rationalParameterDerivative K ((A₀) j)))) /
          algebraMap (L) κ (n₀) := by
    ext i j
    rw [Matrix.map_apply, actual_closed_gauss_graph_hessian_formula H I p hY h hh e hGauss hd hH]
    simp only [map_div₀, map_neg, map_mul]
  rw [hB] at he
  exact (rank_one_quotient_isotropic_iff _ _ _
    ((map_ne_zero (algebraMap (L) κ)).mpr
      (actual_closed_gauss_graph_denominator_ne_zero H I p hY h hh e hGauss hd hH))).mp he

/-- The original coefficient data in any algebraic coefficient
extension satisfy D_b²(nc)=0 for every parameter-algebraic ruling
direction satisfying the actual modified boundary equation. -/
theorem actual_closed_gauss_algebraic_boundary_zero_acceleration
    (c : L) (E : Type u) [Field E] [Algebra (L) E] [Algebra K E]
    [IsScalarTower K (L) E] [Algebra.IsAlgebraic (L) E]
    (v : Fin 3 → E)
    (hv : (fun i => algebraMap (L) E ((f₀) (rationalParameterDerivative K ((A₀) i)))) ⬝ᵥ v = 0)
    (halg : ∀ i, IsAlgebraic (((IsScalarTower.toAlgHom K (L) E).comp (f₀)).fieldRange) (v i))
    (hboundary : matrixBilinearPairing ((coefficientHessian (Y) hY c).map (algebraMap (L) E)) v v -
      (2 / 3 : E) * ((fun i => algebraMap (L) E ((Λ₀) i)) ⬝ᵥ v) *
        ((fun i => algebraMap (L) E (coefficientPartial (Y) hY i c)) ⬝ᵥ v) = 0) :
    coordinateEuler v (extendedCoefficientPartial (Y) hY E)
      (coordinateEuler v (extendedCoefficientPartial (Y) hY E) (algebraMap (L) E ((n₀) * c))) = 0 := by
  let g := IsScalarTower.toAlgHom K (L) E
  let f := g.comp (f₀)
  let δ := extendedCoefficientPartial (Y) hY E
  let y := fun i => g ((y₀) i)
  have hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0 :=
    extendedCoefficientPartial_coordinate (Y) hY E
  have htangent : (fun i => f (rationalParameterDerivative K ((A₀) i))) ⬝ᵥ y = 0 := by
    simpa [f, y, dotProduct] using congrArg g
      (actual_closed_gauss_graph_ruling_equation H I p hY h hh e hd hH)
  have hfirst : (fun i => f (rationalParameterDerivative K ((A₀) i))) ≠ 0 := by
    intro hz
    apply actual_closed_gauss_graph_gradient_derivative_ne_zero H I p hY h hh e hGauss
    funext i
    apply g.injective
    simpa [f, g] using congrFun hz i
  have hΛ : parametricGraphCubicCovector f (A₀) y = fun i => g ((Λ₀) i) :=
    funext (parametricGraphCubicCovector_map (f₀) g (A₀) (y₀))
  have hbound : matrixBilinearPairing (derivationHessian δ (g c)) v v -
      (2 / 3 : E) * (parametricGraphCubicCovector f (A₀) y ⬝ᵥ v) * ((fun i => δ i (g c)) ⬝ᵥ v) = 0 := by
    rw [hΛ]
    simp only [δ, g, IsScalarTower.toAlgHom_apply, extendedCoefficientPartial_hessian,
      extendedCoefficientPartial_extends]
    exact hboundary
  have he := parametric_ruling_zero_acceleration_of_modified_boundary f δ y hcoord (A₀) htangent hfirst
    v hv halg (g c) hbound
  rw [parametricRulingDenominator_map (f₀) g (A₀) (y₀)] at he
  simpa only [δ, g, IsScalarTower.toAlgHom_apply, map_mul] using he

/-- The original actual fiber equations and a parameter-algebraic
residue boundary direction imply the actual zero acceleration in (4.3).
Ruling membership, the modified-quadric equation, direction constancy,
the denominator and the cubic linear factor are all derived internally.
The existence of such a fixed finite boundary branch is not asserted. -/
theorem actual_closed_gauss_parameter_algebraic_residue_boundary_zero_acceleration
    (c q k : L)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q)
    (E : Type u) [Field E] [Algebra (L) E] [Algebra K E]
    [IsScalarTower K (L) E] [Algebra.IsAlgebraic (L) E]
    {O : Type u} [CommRing O] [Algebra (L) O] [Algebra O S₀] [IsScalarTower (L) O S₀]
    (π : O →ₐ[L] E) (hinj : Function.Injective (algebraMap O S₀))
    (s : S₀) (z : Option (Fin 3) → O)
    (hz0 : algebraMap O S₀ (z none) = s)
    (hz : ∀ i, algebraMap O S₀ (z (some i)) = s * rationalCoordinate (K := K) (p i.castSucc))
    (hres0 : π (z none) = 0)
    (halg : ∀ i, IsAlgebraic (((IsScalarTower.toAlgHom K (L) E).comp (f₀)).fieldRange) (π (z (some i)))) :
    coordinateEuler (fun i => π (z (some i))) (extendedCoefficientPartial (Y) hY E)
      (coordinateEuler (fun i => π (z (some i))) (extendedCoefficientPartial (Y) hY E)
        (algebraMap (L) E ((n₀) * c))) = 0 :=
  actual_closed_gauss_algebraic_boundary_zero_acceleration H I p hY h hh e hGauss hd hH c E
    (fun i => π (z (some i)))
    (actual_closed_gauss_quadratic_boundary_mem_ruling H I p hY h hh e hGauss hd hH
      c q hq π hinj s z hz0 hz hres0) halg
    (actual_closed_gauss_modified_cubic_boundary_equation H I p hY h hh e hGauss hd hH
      c q k hq hk π hinj s z hz0 hz hres0)

end DimensionFourDependence
