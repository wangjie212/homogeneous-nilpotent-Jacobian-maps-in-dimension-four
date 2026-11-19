import DimensionFourDependence.FiberBoundaryCoefficientExtension
import DimensionFourDependence.ProjectiveBoundaryProjection
import DimensionFourDependence.FiniteGaussActualBoundaryLocalBound
import DimensionFourDependence.ActualGaussBoundaryRootConstruction

/-! # The original map's finite root data construct the actual infinity local bound

Keep the original affine fiber over its original coefficient field and
its actual residue-valued boundary. The same extended partials and exact
coefficient maps identify the constructed chart equations with the
original leading equations. The finite root construction's s(v)=0
identifies its specified chart point with that actual boundary point.
-/

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

/-- At the actual original residue-valued boundary, independent finite
root forms construct an invertible chart, identify its specified fixed
point with the actual projected closure point, and prove the entire
original coefficient-extended infinity chart's local length at most two.
No common overfield, assumed equation membership, simple jets, point
identification or local quotient map is supplied. -/
theorem actual_closed_gauss_independent_root_boundary_chart_local_bound
    {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d) (hGauss : gaussImageDimension H I = 1)
    (c q k : L) (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q)
    (z : Option (Fin 4) → F) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (x))
    (hz0 : z none = 0) (hv0 : (fun i : Fin 3 => z (some (p i.castSucc))) ≠ 0)
    (C : IntermediateField (f).fieldRange F) [Module.Finite (f).fieldRange C]
    (m s : Fin 3 → C)
    (hpair : LinearIndependent C ![rulingFormRestriction (finiteParameterGraphRuling (f) C (A₀)) m,
      rulingFormRestriction (finiteParameterGraphRuling (f) C (A₀)) s])
    (rho : F) (hrho : rho ≠ 0)
    (hprod : (g) (n₀) * (g) c = ((fun i => (m i : F)) ⬝ᵥ (y)) * rho)
    (hroot : rho ^ d = (fun i => (s i : F)) ⬝ᵥ (y))
    (hsv : (fun i => (s i : F)) ⬝ᵥ (fun i : Fin 3 => z (some (p i.castSucc))) = 0) :
    ∃ w a b : Fin 3 → C,
      (rulingBoundaryCoordinateMatrix w a b).det ≠ 0 ∧
      (rulingBoundaryCoordinateMatrix (fun i => (w i : F)) (fun i => (a i : F)) (fun i => (b i : F))).det ≠ 0 ∧
      ∃ hb : (fun i => (b i : F)) ≠ 0,
        projectiveFieldPoint (E := L) (fun j : Option (Fin 3) => j.elim 0 (fun i => (b i : F)))
          (infinity_direction_projective_coordinates_ne_zero _ hb) ∈ projectiveClosureSet («L» := L) (x₃) ∧
        HasOriginLocalLengthAtMostTwo
          (extendedProjectiveInfinityChartIdeal (E := L) (x₃)
            (fun i => (b i : F)) (fun i => (w i : F)) (fun i => (a i : F))) := by
  let : CharZero (L) := charZero_of_injective_algebraMap (algebraMap K (L)).injective
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have hd0 : 0 < d := by omega
  have hcoord : ∀ i j, (delta) i ((y) j) = if j = i then 1 else 0 :=
    extendedCoefficientPartial_coordinate (Y) hY F
  have htangent : (fun i => (f) (rationalParameterDerivative K ((A₀) i))) ⬝ᵥ (y) = 0 := by
    simpa only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, dotProduct, map_sum, map_mul, map_zero] using
      congrArg (g) (actual_closed_gauss_graph_ruling_equation H I p hY h hh e hd0 hH)
  have hfirst : (fun i => (f) (rationalParameterDerivative K ((A₀) i))) ≠ 0 := by
    intro hzero
    apply actual_closed_gauss_graph_gradient_derivative_ne_zero H I p hY h hh e hGauss
    funext i
    apply (g).injective
    change (g) ((f₀) (rationalParameterDerivative K ((A₀) i))) = (g) 0
    rw [map_zero]
    exact congrFun hzero i
  have hgradient : ∀ i, (delta) i ((g) h) = (f) ((A₀) i) := by
    intro i
    change (delta) i (algebraMap (L) F h) = algebraMap (L) F ((f₀) ((A₀) i))
    rw [extendedCoefficientPartial_extends, closedGaussCoefficientGraphSlope_value]
  have hfactor : parametricRulingDenominator (f) (A₀) (y) * (g) c =
      ((fun i => (m i : F)) ⬝ᵥ (y)) * rho := by
    rw [parametricRulingDenominator_map]
    exact hprod
  obtain ⟨w, a, b, _hw, hb, ha, hmb, hsb, hma, hsa, hdet, hdetF,
      hsecond, htransverse, hfirstChart, _hpairIdeal, _hpairLocal⟩ :=
    finite_parameter_graph_constructs_actual_simple_boundary_intersection (f) (delta) (y) hcoord
      (extendedCoefficientPartials_commute (Y) hY F) (A₀) htangent hfirst ((g) h) hgradient
      C m s hpair hd0 rho ((g) c) ((g) q) hrho hfactor hroot
  let v : Fin 3 → F := fun i => z (some (p i.castSucc))
  have hiso := projective_fiber_closure_quadratic_isotropic (x) z hz hpoint hz0
    (fun i : Fin 3 => p i.castSucc) (coefficientGradient (Y) hY c) (coefficientHessian (Y) hY h) q
    (quadraticFiberEquation_aeval_zero p (Y) hY h c q hq)
  have hB : (coefficientHessian (Y) hY h).map (algebraMap (L) F) =
      fun i j => -((f) (rationalParameterDerivative K ((A₀) i)) *
        (f) (rationalParameterDerivative K ((A₀) j))) / parametricRulingDenominator (f) (A₀) (y) := by
    ext i j
    rw [Matrix.map_apply, actual_closed_gauss_graph_hessian_formula H I p hY h hh e hGauss hd0 hH]
    rw [parametricRulingDenominator_map]
    simp only [map_div₀, map_neg, map_mul, AlgHom.comp_apply,
      IsScalarTower.toAlgHom_apply]
  rw [hB] at hiso
  have hv : (fun i => (f) (rationalParameterDerivative K ((A₀) i))) ⬝ᵥ v = 0 :=
    (rank_one_quotient_isotropic_iff _ _ _
      (parametric_ruling_denominator_ne_zero (f) (delta) (y) hcoord (A₀) htangent hfirst)).mp hiso
  have hcoordinates := finite_parameter_graph_coordinates_of_specified_dual_pair (f) C (A₀) hfirst
    m s b a hpair hb ha hmb hsb hma hsa v hv
  have hrep : v = ((fun i => (m i : F)) ⬝ᵥ v) • (fun i => (b i : F)) := by
    funext i
    change v i = ((fun j => (m j : F)) ⬝ᵥ v) * (b i : F)
    have hi := hcoordinates i
    rw [hsv, mul_zero, add_zero] at hi
    exact hi.trans (mul_comm _ _)
  have ht : ((fun i => (m i : F)) ⬝ᵥ v) ≠ 0 := by
    intro hzero
    apply hv0
    change v = 0
    rw [hrep, hzero, zero_smul]
  have hprojection : z ∘ Option.map (fun i : Fin 3 => p i.castSucc) =
      (fun j : Option (Fin 3) => j.elim 0 v) := by
    funext j
    cases j <;> simp only [Function.comp_def, Option.map_none, Option.map_some, Option.elim_none,
      Option.elim_some, hz0, v]
  have hp0 : z ∘ Option.map (fun i : Fin 3 => p i.castSucc) ≠ 0 := by
    rw [hprojection]
    exact infinity_direction_projective_coordinates_ne_zero v hv0
  have hprojected := projective_closure_point_coordinate_projection (x) z hz hpoint
    (fun i : Fin 3 => p i.castSucc) hp0
  have hpointEq := projectiveFieldPoint_eq_of_coordinate_eq (E := L)
    _ _ hp0 (infinity_direction_projective_coordinates_ne_zero v hv0) hprojection
  rw [hpointEq] at hprojected
  obtain ⟨hbF, hbpoint⟩ := projective_closure_extension_infinity_point_of_nonzero_smul (x₃) v
    (fun i => (b i : F)) hv0 hprojected ((fun i => (m i : F)) ⬝ᵥ v) ht hrep
  have hgrad : (fun i => algebraMap (L) F (coefficientPartial (Y) hY i c)) =
      (fun i => (delta) i ((g) c)) := by
    funext i
    exact (extendedCoefficientPartial_extends (Y) hY F i c).symm
  have hHmap := (extendedCoefficientPartial_hessian (Y) hY F h).symm
  have hCmap := (extendedCoefficientPartial_hessian (Y) hY F c).symm
  have hLambda : (fun i => algebraMap (L) F ((Λ₀) i)) = parametricGraphCubicCovector (f) (A₀) (y) := by
    funext i
    exact (parametricGraphCubicCovector_map (f₀) (g) (A₀) (y₀) i).symm
  have hfirstMap : MvPolynomial.map (algebraMap (L) F)
      (homogeneousComponent 2 (quadraticFiberPolynomial (coefficientGradient (Y) hY c)
        (coefficientHessian (Y) hY h) q)) =
      homogeneousComponent 2 (quadraticFiberPolynomial (fun i => (delta) i ((g) c))
        (derivationHessian (delta) ((g) h)) ((g) q)) := by
    rw [quadraticFiberPolynomial_leading_map_coefficients, hHmap]
    exact congrArg (fun a => homogeneousComponent 2
      (quadraticFiberPolynomial a (derivationHessian (delta) ((g) h)) ((g) q))) hgrad
  have hsecondMap : MvPolynomial.map (algebraMap (L) F)
      (modifiedBoundaryQuadric (coefficientGradient (Y) hY c) (Λ₀) (coefficientHessian (Y) hY c)) =
      modifiedBoundaryQuadric (fun i => (delta) i ((g) c))
        (parametricGraphCubicCovector (f) (A₀) (y)) (derivationHessian (delta) ((g) c)) := by
    rw [modifiedBoundaryQuadric_map_coefficients, hCmap, hLambda]
    exact congrArg (fun a => modifiedBoundaryQuadric a (parametricGraphCubicCovector (f) (A₀) (y))
      (derivationHessian (delta) ((g) c))) hgrad
  refine ⟨w, a, b, hdet, hdetF, hbF, hbpoint, ?_⟩
  apply original_closure_extended_infinity_chart_origin_local_bound (x₃) _ _ _
    (coefficientGradient (Y) hY c) (coefficientGradient (Y) hY q) (Λ₀) hbF hbpoint
    (coefficientHessian (Y) hY h) (coefficientHessian (Y) hY c) (coefficientCubicTensor (Y) hY h) q k
    (actual_closed_gauss_graph_cubic_polynomial_factorization H I p hY h hh e hGauss hd0 hH)
    (quadraticFiberEquation_aeval_zero p (Y) hY h c q hq)
    (cubicFiberEquation_aeval_zero p (Y) hY h c q k hk)
    ((2 : F)⁻¹ * (-(parametricRulingDenominator (f) (A₀) (y))⁻¹))
    (mul_ne_zero (inv_ne_zero (by norm_num))
      (neg_ne_zero.mpr (inv_ne_zero (parametric_ruling_denominator_ne_zero (f) (delta) (y) hcoord (A₀) htangent hfirst))))
  · rwa [hfirstMap]
  · rwa [hsecondMap]
  · rwa [hsecondMap]

end DimensionFourDependence
