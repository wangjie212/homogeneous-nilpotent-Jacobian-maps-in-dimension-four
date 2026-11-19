import DimensionFourDependence.FiniteRootBoundaryFieldExtension
import DimensionFourDependence.ActualInfinityPrimeAlgebraicity
import DimensionFourDependence.BoundaryGaussFieldComparison
import DimensionFourDependence.ProjectiveModifiedBoundaryEquation
import DimensionFourDependence.ActualDevelopableBoundaryEquation
import DimensionFourDependence.ActualBoundaryGraphDirection

/-! # The original fixed vector controls every normalized algebraic boundary

The original quadratic and cubic invariant equations derive ruling
membership and the modified boundary equation in any further algebraic
coordinate field. The original ruling-preservation argument supplies
parameter algebraicity there. The same finite root forms and same dual
vector therefore control all these actual boundary points.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

attribute [local instance] coefficientFieldScalarTower

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (p : Equiv.Perm (Fin 4))
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
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh e
local notation "A₀" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "y₀" => coefficientCoordinate (K := K) (Y)
local notation "n₀" => parametricRulingDenominator (f₀) (A₀) (y₀)
local notation "Λ₀" => parametricGraphCubicCovector (f₀) (A₀) (y₀)

variable (F R : Type u) [Field F] [Field R]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) F]
    [Algebra K F]
    [IsScalarTower K (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) F]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) R]
    [Algebra K R] [Algebra F R] [IsScalarTower K F R]
    [IsScalarTower (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) F R]
    [IsScalarTower K (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) R]
    [Algebra.IsAlgebraic (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) R]

local notation "gF" => IsScalarTower.toAlgHom K (L) F
local notation "gR" => IsScalarTower.toAlgHom K (L) R
local notation "gFR" => IsScalarTower.toAlgHom K F R
local notation "fF" => (gF).comp (f₀)
local notation "fR" => (gFR).comp (fF)
local notation "yF" => fun i => (gF) ((y₀) i)
local notation "yR" => fun i => (gFR) ((yF) i)
local notation "delta" => extendedCoefficientPartial (Y) hY R

include hrank

/-- Every normalized actual boundary point in every compatible
algebraic coordinate field is proportional, in its projected graph
coordinates, to the same specified original finite dual vector.
All parameter algebraicity and both boundary equations are derived
from the original map and its actual projective closure. -/
theorem actual_normalized_boundary_multiple_of_same_finite_simple_root
    {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (c q k : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q)
    (C : IntermediateField (fF).fieldRange F) [Module.Finite (fF).fieldRange C]
    (m s b a : Fin 3 → C)
    (hpair : LinearIndependent C ![rulingFormRestriction (finiteParameterGraphRuling (fF) C (A₀)) m,
      rulingFormRestriction (finiteParameterGraphRuling (fF) C (A₀)) s])
    (hb : b ∈ finiteParameterGraphRuling (fF) C (A₀)) (ha : a ∈ finiteParameterGraphRuling (fF) C (A₀))
    (hmb : m ⬝ᵥ b = 1) (hsb : s ⬝ᵥ b = 0) (hma : m ⬝ᵥ a = 0) (hsa : s ⬝ᵥ a = 1)
    (rho : F) (hrho : rho ≠ 0)
    (hprod : (gF) (n₀) * (gF) c = ((fun i => (m i : F)) ⬝ᵥ (yF)) * rho)
    (hroot : rho ^ d = (fun i => (s i : F)) ⬝ᵥ (yF))
    (z : Option (Fin 4) → R) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (x))
    (hz0 : z none = 0) (j : Fin 4) (hj : z (some j) = 1) :
    ∃ t : R, t ≠ 0 ∧ (fun i : Fin 3 => z (some (p i.castSucc))) =
      t • (fun i => (gFR) (b i : F)) := by
  let : CharZero (L) := charZero_of_injective_algebraMap (algebraMap K (L)).injective
  let : CharZero R := charZero_of_injective_algebraMap (algebraMap K R).injective
  have hd0 : 0 < d := by omega
  have hfR : (fR) = (gR).comp (f₀) := by
    apply AlgHom.ext
    intro r
    change algebraMap F R (algebraMap (L) F ((f₀) r)) = algebraMap (L) R ((f₀) r)
    exact (IsScalarTower.algebraMap_apply (L) F R _).symm
  have hyR : (yR) = fun i => (gR) ((y₀) i) := by
    funext i
    exact (IsScalarTower.algebraMap_apply (L) F R _).symm
  have hcR : (gFR) ((gF) c) = (gR) c := (IsScalarTower.algebraMap_apply (L) F R _).symm
  have hcoord : ∀ i j, (delta) i ((gFR) ((yF) j)) = if j = i then 1 else 0 := by
    intro i j
    change (delta) i (algebraMap F R (algebraMap (L) F ((y₀) j))) = _
    rw [← IsScalarTower.algebraMap_apply (L) F R]
    exact extendedCoefficientPartial_coordinate (Y) hY R i j
  have htangent : (fun i => (fF) (rationalParameterDerivative K ((A₀) i))) ⬝ᵥ (yF) = 0 := by
    simpa only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, dotProduct, map_sum, map_mul, map_zero] using
      congrArg (gF) (actual_closed_gauss_graph_ruling_equation H I p hY h hh e hd0 hH)
  have hfirst : (fun i => (fF) (rationalParameterDerivative K ((A₀) i))) ≠ 0 := by
    intro hzero
    apply actual_closed_gauss_graph_gradient_derivative_ne_zero H I p hY h hh e hGauss
    funext i
    apply (gF).injective
    change (gF) ((f₀) (rationalParameterDerivative K ((A₀) i))) = (gF) 0
    simpa only [map_zero, AlgHom.comp_apply, Pi.zero_apply] using congrFun hzero i
  have hfactor : parametricRulingDenominator (fF) (A₀) (yF) * (gF) c =
      ((fun i => (m i : F)) ⬝ᵥ (yF)) * rho := by
    rw [parametricRulingDenominator_map]
    exact hprod
  let v : Fin 3 → R := fun i => z (some (p i.castSucc))
  have hfull : (fun i : Fin 4 => z (some i)) ≠ 0 := by
    intro hzero
    have he := congrFun hzero j
    rw [hj] at he
    exact one_ne_zero he
  have hv0 : v ≠ 0 := actual_full_fiber_boundary_first_three_direction_ne_zero H p hY h c hc R
    z hz hfull hpoint hz0
  have halgFull := actual_full_fiber_boundary_coordinates_algebraic_over_original_gauss H hrank p hY
    hd0 hH hN hind I hGauss h c q hh hc hq R z hz hfull hpoint hz0 j hj
  have halg : ∀ i, IsAlgebraic (fR).fieldRange (v i) := by
    rw [hfR]
    intro i
    exact actual_boundary_original_gauss_algebraic_implies_closed_parameter_algebraic H hrank I p hY h hh e R
      _ (halgFull (p i.castSucc))
  have hiso := projective_fiber_closure_quadratic_isotropic (x) z hz hpoint hz0
    (fun i : Fin 3 => p i.castSucc) (coefficientGradient (Y) hY c) (coefficientHessian (Y) hY h) q
    (quadraticFiberEquation_aeval_zero p (Y) hY h c q hq)
  have hB : (coefficientHessian (Y) hY h).map (algebraMap (L) R) =
      fun i j => -((fR) (rationalParameterDerivative K ((A₀) i)) *
        (fR) (rationalParameterDerivative K ((A₀) j))) / parametricRulingDenominator (fR) (A₀) (yR) := by
    rw [hfR, hyR, parametricRulingDenominator_map]
    ext i j
    rw [Matrix.map_apply, actual_closed_gauss_graph_hessian_formula H I p hY h hh e hGauss hd0 hH]
    simp only [map_div₀, map_neg, map_mul, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]
  rw [hB] at hiso
  have hdenom : parametricRulingDenominator (fR) (A₀) (yR) ≠ 0 := by
    rw [hfR, hyR, parametricRulingDenominator_map]
    exact (map_ne_zero (gR)).mpr (actual_closed_gauss_graph_denominator_ne_zero H I p hY h hh e hGauss hd0 hH)
  have hv : (fun i => (fR) (rationalParameterDerivative K ((A₀) i))) ⬝ᵥ v = 0 :=
    (rank_one_quotient_isotropic_iff _ _ _ hdenom).mp hiso
  have hboundary := projective_closure_modified_cubic_boundary_equation (x) z hz hpoint hz0
    (fun i : Fin 3 => p i.castSucc) (coefficientGradient (Y) hY c) (coefficientGradient (Y) hY q) (Λ₀)
    (coefficientHessian (Y) hY h) (coefficientHessian (Y) hY c) (coefficientCubicTensor (Y) hY h) q k
    (actual_closed_gauss_graph_cubic_polynomial_factorization H I p hY h hh e hGauss hd0 hH)
    (quadraticFiberEquation_aeval_zero p (Y) hY h c q hq) (cubicFiberEquation_aeval_zero p (Y) hY h c q k hk)
  have hHess : derivationHessian (delta) ((gFR) ((gF) c)) =
      (coefficientHessian (Y) hY c).map (algebraMap (L) R) := by
    rw [hcR]
    exact extendedCoefficientPartial_hessian (Y) hY R c
  have hgrad : (fun i => (delta) i ((gFR) ((gF) c))) =
      fun i => algebraMap (L) R (coefficientPartial (Y) hY i c) := by
    rw [hcR]
    funext i
    exact extendedCoefficientPartial_extends (Y) hY R i c
  have hLambda : parametricGraphCubicCovector (fR) (A₀) (yR) =
      fun i => algebraMap (L) R ((Λ₀) i) := by
    rw [hfR, hyR]
    funext i
    exact parametricGraphCubicCovector_map (f₀) (gR) (A₀) (y₀) i
  have hboundaryR : matrixBilinearPairing (derivationHessian (delta) ((gFR) ((gF) c))) v v -
      (2 / 3 : R) * (parametricGraphCubicCovector (fR) (A₀) (yR) ⬝ᵥ v) *
        ((fun i => (delta) i ((gFR) ((gF) c))) ⬝ᵥ v) = 0 := by
    rw [hHess, hgrad, hLambda]
    exact hboundary
  exact finite_root_boundary_multiple_of_same_dual_point_after_field_embedding (fF) (gFR) (delta)
    (yF) hcoord (A₀) htangent hfirst C m s b a hpair hb ha hmb hsb hma hsa
    hd rho ((gF) c) hrho hfactor hroot v hv0 hv halg hboundaryR

end DimensionFourDependence
