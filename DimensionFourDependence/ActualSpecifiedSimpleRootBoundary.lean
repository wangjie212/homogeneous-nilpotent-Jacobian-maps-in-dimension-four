import DimensionFourDependence.ActualUniformSimpleBoundaryDirection
import DimensionFourDependence.GraphRulingCovectorProjection

/-! # Actual boundary equations force the specified finite root form to vanish -/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
local notation "Y" => (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc)))
local notation "L" => coefficientField (K := K) (Y)
local notation "x" => rationalCoordinate (K := K) (n := 4)
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh e
local notation "A₀" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "y₀" => coefficientCoordinate (K := K) (Y)
local notation "n₀" => parametricRulingDenominator (f₀) (A₀) (y₀)
local notation "Λ₀" => parametricGraphCubicCovector (f₀) (A₀) (y₀)

variable (R : Type u) [Field R]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) R]
    [Algebra K R]
    [IsScalarTower K (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) R]
    [Algebra.IsAlgebraic (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) R]

local notation "g" => IsScalarTower.toAlgHom K (L) R
local notation "f" => (g).comp (f₀)
local notation "y" => (fun i => (g) ((y₀) i))
local notation "delta" => extendedCoefficientPartial (Y) hY R

include hrank

/-- The actual original fiber boundary annihilates the specified
root form. All boundary equations and direction algebraicity follow
from the original map and its closure. Only one specified longitudinal
vector and its two actual dual values are needed; a new finite field
or a new dual basis at the boundary is unnecessary. -/
theorem actual_normalized_boundary_annihilates_specified_simple_root_form
    {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (c q k : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q)
    (m s b : Fin 3 → R)
    (hm : ∀ i, IsAlgebraic (f).fieldRange (m i))
    (hs : ∀ i, IsAlgebraic (f).fieldRange (s i))
    (hb : (fun i => (f) (rationalParameterDerivative K ((A₀) i))) ⬝ᵥ b = 0)
    (hmb : m ⬝ᵥ b = 1) (hsb : s ⬝ᵥ b = 0)
    (rho : R) (hrho : rho ≠ 0)
    (hprod : (g) (n₀) * (g) c = (m ⬝ᵥ (y)) * rho)
    (hroot : rho ^ d = s ⬝ᵥ (y))
    (z : Option (Fin 4) → R) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (x))
    (hz0 : z none = 0) (j : Fin 4) (hj : z (some j) = 1) :
    s ⬝ᵥ (fun i : Fin 3 => z (some (p i.castSucc))) = 0 := by
  letI : CharZero (L) := charZero_of_injective_algebraMap (algebraMap K (L)).injective
  letI : CharZero R := charZero_of_injective_algebraMap (algebraMap K R).injective
  have hd0 : 0 < d := by omega
  have hcoord : ∀ i j, (delta) i ((y) j) = if j = i then 1 else 0 :=
    extendedCoefficientPartial_coordinate (Y) hY R
  have htangent : (fun i => (f) (rationalParameterDerivative K ((A₀) i))) ⬝ᵥ (y) = 0 := by
    simpa only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, dotProduct, map_sum, map_mul, map_zero] using
      congrArg (g) (actual_closed_gauss_graph_ruling_equation H I p hY h hh e hd0 hH)
  have hfirst : (fun i => (f) (rationalParameterDerivative K ((A₀) i))) ≠ 0 := by
    intro hzero
    apply actual_closed_gauss_graph_gradient_derivative_ne_zero H I p hY h hh e hGauss
    funext i
    apply (g).injective
    change (g) ((f₀) (rationalParameterDerivative K ((A₀) i))) = (g) 0
    simpa only [map_zero, AlgHom.comp_apply, Pi.zero_apply] using congrFun hzero i
  have hfactor : parametricRulingDenominator (f) (A₀) (y) * (g) c = (m ⬝ᵥ (y)) * rho := by
    rw [parametricRulingDenominator_map]
    exact hprod
  let v : Fin 3 → R := fun i => z (some (p i.castSucc))
  have hfull : (fun i : Fin 4 => z (some i)) ≠ 0 := by
    intro hzero
    have he := congrFun hzero j
    rw [hj] at he
    exact one_ne_zero he
  have halgFull := actual_full_fiber_boundary_coordinates_algebraic_over_original_gauss H hrank p hY
    hd0 hH hN hind I hGauss h c q hh hc hq R z hz hfull hpoint hz0 j hj
  have halg : ∀ i, IsAlgebraic (f).fieldRange (v i) := by
    intro i
    exact actual_boundary_original_gauss_algebraic_implies_closed_parameter_algebraic H hrank I p hY h hh e R
      _ (halgFull (p i.castSucc))
  have hiso := projective_fiber_closure_quadratic_isotropic (x) z hz hpoint hz0
    (fun i : Fin 3 => p i.castSucc) (coefficientGradient (Y) hY c) (coefficientHessian (Y) hY h) q
    (quadraticFiberEquation_aeval_zero p (Y) hY h c q hq)
  have hB : (coefficientHessian (Y) hY h).map (algebraMap (L) R) =
      fun i j => -((f) (rationalParameterDerivative K ((A₀) i)) *
        (f) (rationalParameterDerivative K ((A₀) j))) / parametricRulingDenominator (f) (A₀) (y) := by
    rw [parametricRulingDenominator_map]
    ext i j
    rw [Matrix.map_apply, actual_closed_gauss_graph_hessian_formula H I p hY h hh e hGauss hd0 hH]
    simp only [map_div₀, map_neg, map_mul, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]
  rw [hB] at hiso
  have hdenom : parametricRulingDenominator (f) (A₀) (y) ≠ 0 := by
    rw [parametricRulingDenominator_map]
    exact (map_ne_zero (g)).mpr (actual_closed_gauss_graph_denominator_ne_zero H I p hY h hh e hGauss hd0 hH)
  have hv : (fun i => (f) (rationalParameterDerivative K ((A₀) i))) ⬝ᵥ v = 0 :=
    (rank_one_quotient_isotropic_iff _ _ _ hdenom).mp hiso
  have hboundary := projective_closure_modified_cubic_boundary_equation (x) z hz hpoint hz0
    (fun i : Fin 3 => p i.castSucc) (coefficientGradient (Y) hY c) (coefficientGradient (Y) hY q) (Λ₀)
    (coefficientHessian (Y) hY h) (coefficientHessian (Y) hY c) (coefficientCubicTensor (Y) hY h) q k
    (actual_closed_gauss_graph_cubic_polynomial_factorization H I p hY h hh e hGauss hd0 hH)
    (quadraticFiberEquation_aeval_zero p (Y) hY h c q hq) (cubicFiberEquation_aeval_zero p (Y) hY h c q k hk)
  have hHess : derivationHessian (delta) ((g) c) = (coefficientHessian (Y) hY c).map (algebraMap (L) R) :=
    extendedCoefficientPartial_hessian (Y) hY R c
  have hgrad : (fun i => (delta) i ((g) c)) =
      fun i => algebraMap (L) R (coefficientPartial (Y) hY i c) :=
    funext (fun i => extendedCoefficientPartial_extends (Y) hY R i c)
  have hLambda : parametricGraphCubicCovector (f) (A₀) (y) =
      fun i => algebraMap (L) R ((Λ₀) i) :=
    funext (parametricGraphCubicCovector_map (f₀) (g) (A₀) (y₀))
  have hboundaryR : matrixBilinearPairing (derivationHessian (delta) ((g) c)) v v -
      (2 / 3 : R) * (parametricGraphCubicCovector (f) (A₀) (y) ⬝ᵥ v) *
        ((fun i => (delta) i ((g) c)) ⬝ᵥ v) = 0 := by
    rw [hHess, hgrad, hLambda]
    exact hboundary
  exact parametric_simple_root_boundary_fixed_of_specified_dual_direction (f) (delta) (y) hcoord
    (A₀) htangent hfirst m s b hm hs hb hmb hsb hd rho ((g) c) hrho hfactor hroot v hv halg hboundaryR

/-- In the original four coordinate labels, the specified output
covector itself annihilates the entire actual normalized boundary.
The graph first-invariant equation supplies the omitted coordinate. -/
theorem actual_full_boundary_annihilates_original_specified_root_covector
    {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (c q k : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q)
    (m : Fin 3 → R) (S : Fin 4 → R) (b : Fin 3 → R)
    (hm : ∀ i, IsAlgebraic (f).fieldRange (m i))
    (hs : ∀ i, IsAlgebraic (f).fieldRange
      (graphRestrictedCovector p (fun j => (f) ((A₀) j)) S i))
    (hb : (fun i => (f) (rationalParameterDerivative K ((A₀) i))) ⬝ᵥ b = 0)
    (hmb : m ⬝ᵥ b = 1)
    (hsb : graphRestrictedCovector p (fun j => (f) ((A₀) j)) S ⬝ᵥ b = 0)
    (rho : R) (hrho : rho ≠ 0)
    (hprod : (g) (n₀) * (g) c = (m ⬝ᵥ (y)) * rho)
    (hroot : rho ^ d = graphRestrictedCovector p (fun j => (f) ((A₀) j)) S ⬝ᵥ (y))
    (z : Option (Fin 4) → R) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (x))
    (hz0 : z none = 0) (j : Fin 4) (hj : z (some j) = 1) :
    S ⬝ᵥ (fun i => z (some i)) = 0 := by
  have hsroot := actual_normalized_boundary_annihilates_specified_simple_root_form H hrank I p hY h hh e R
    hd hH hN hind hGauss c q k hc hq hk m
    (graphRestrictedCovector p (fun j => (f) ((A₀) j)) S) b hm hs hb hmb hsb rho hrho hprod hroot
    z hz hpoint hz0 j hj
  have hlinear : z (some (p 3)) = ∑ i : Fin 3, (f) ((A₀) i) * z (some (p i.castSucc)) := by
    have he := actual_full_fiber_boundary_graph_linear_equation H p hY h c hc R z hz hpoint hz0
    simpa only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, closedGaussCoefficientGraphSlope_value] using he
  exact (graphRestrictedCovector_pairing p (fun j => (f) ((A₀) j)) S
    (fun i => z (some i)) hlinear).symm.trans hsroot

/-- At the fixed fourth-axis vertex, the original simple-root
covector must have zero fourth coefficient. A nonzero value there
therefore contradicts actual boundary membership. -/
theorem actual_fixed_vertex_boundary_forces_specified_root_fourth_coefficient_zero
    {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (c q k : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q)
    (m : Fin 3 → R) (S : Fin 4 → R) (b : Fin 3 → R)
    (hm : ∀ i, IsAlgebraic (f).fieldRange (m i))
    (hs : ∀ i, IsAlgebraic (f).fieldRange
      (graphRestrictedCovector p (fun j => (f) ((A₀) j)) S i))
    (hb : (fun i => (f) (rationalParameterDerivative K ((A₀) i))) ⬝ᵥ b = 0)
    (hmb : m ⬝ᵥ b = 1)
    (hsb : graphRestrictedCovector p (fun j => (f) ((A₀) j)) S ⬝ᵥ b = 0)
    (rho : R) (hrho : rho ≠ 0)
    (hprod : (g) (n₀) * (g) c = (m ⬝ᵥ (y)) * rho)
    (hroot : rho ^ d = graphRestrictedCovector p (fun j => (f) ((A₀) j)) S ⬝ᵥ (y))
    (z : Option (Fin 4) → R) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (x))
    (hz0 : z none = 0) (hzfirst : ∀ i : Fin 3, z (some i.castSucc) = 0)
    (hzlast : z (some (Fin.last 3)) = 1) : S (Fin.last 3) = 0 := by
  have he := actual_full_boundary_annihilates_original_specified_root_covector H hrank I p hY h hh e R
    hd hH hN hind hGauss c q k hc hq hk m S b hm hs hb hmb hsb rho hrho hprod hroot
    z hz hpoint hz0 (Fin.last 3) hzlast
  unfold dotProduct at he
  rw [Fin.sum_univ_castSucc] at he
  simpa only [hzfirst, hzlast, mul_zero, Finset.sum_const_zero, mul_one, zero_add] using he

end DimensionFourDependence
