import DimensionFourDependence.OriginalGraphRootForms
import DimensionFourDependence.ActualClosedGraphBoundaryRuling
import DimensionFourDependence.ActualSpecifiedSimpleRootBoundary
import DimensionFourDependence.SpecifiedRulingDualCoordinates
import DimensionFourDependence.GraphBoundaryFixedAxis

/-! # The original independent root forms force the original fixed vertex at infinity -/

namespace DimensionFourDependence

open Matrix Module MvPolynomial

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [fieldK : Field K] [charK : CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (E : Type u) [fieldE : Field E] [algCE : Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "C₀" => closedGaussParameterField H I
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "a₀" => actualClosedGaussCoefficientHom H I p hY h hh
local notation "A" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "Aₑ" => fun i => algebraMap C₀ E (e ((A) i))
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh e
local notation "W₀" => LinearMap.ker ((extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin' : (Fin 4 → E) →ₗ[E] (Fin 2 → E))

variable (κ : Type u) [Field κ] [Algebra K κ] [Algebra (coefficientField (K := K)
    (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
      (H (p i.castSucc)))) κ]
    [IsScalarTower K (coefficientField (K := K)
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
        (H (p i.castSucc)))) κ] [Algebra E κ]

local notation "g" => IsScalarTower.toAlgHom K (L) κ
local notation "f" => (g).comp (f₀)

variable [Algebra.IsAlgebraic (coefficientField (K := K)
    (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
      (H (p i.castSucc)))) κ]

local notation "yκ" => fun i => (g) (coefficientCoordinate (K := K) (Y) i)
local notation "n₀" => parametricRulingDenominator (f₀) (A) (coefficientCoordinate (K := K) (Y))

/-- The original independent root forms force the actual original
fourth-axis point to lie in the full-fiber closure. -/
theorem independent_original_graph_root_forms_construct_original_vertex_boundary
    (hrank : polyRank (jac H) = 3) (hN : IsNilpotent (jac H)) (hd1 : 1 < d)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (hcompat :
      letI : Algebra C₀ κ := ((algebraMap (L) κ).comp (a₀).toRingHom).toAlgebra
      IsScalarTower C₀ E κ)
    (c q k : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q)
    (hforms : IndependentOriginalGraphRootForms H I p hY h hh E hH hd hind hGauss e κ c)
    (z : Option (Fin 4) → κ) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L)
      (rationalCoordinate (K := K) (n := 4)))
    (hz0 : z none = 0) (j : Fin 4) (hj : z (some j) = 1) :
    fourthAxisAffineInfinityPoint (L) ∈ projectiveClosureSet («L» := L)
      (rationalCoordinate (K := K) (n := 4)) := by
  obtain ⟨M, S, rho, hM, hS, hrho, hprod, hroot, hpair⟩ := hforms
  have hbase := @fixed_vertex_root_forms_construct_explicit_original_graph_basis_witnesses
    K fieldK charK H I p hY h hh e E fieldE algCE d hH hd hind hGauss hvertex M S hM hS hpair
  obtain ⟨bE, aE, hbEq, hbE, _haE, hbgraph, hagraph, hmb, hsb, hma, hsa⟩ := hbase
  let : Algebra C₀ κ := ((algebraMap (L) κ).comp (a₀).toRingHom).toAlgebra
  let : IsScalarTower C₀ E κ := hcompat
  let gC := (g).comp (a₀)
  let σ := algebraMap E κ
  have hσ (b : C₀) : σ (algebraMap C₀ E b) = gC b :=
    (IsScalarTower.algebraMap_apply C₀ E κ b).symm
  have hf : gC.comp e.toAlgHom = (f) := by
    apply AlgHom.ext
    intro r
    exact congrArg (g) (actualClosedGaussCoefficientHom_parameter_value H I p hY h hh e r)
  have halg (b : E) : IsAlgebraic (f).fieldRange (σ b) := by
    rw [← hf]
    exact specified_algebraic_coefficient_image_algebraic_over_same_parameter e gC σ hσ b
  have hscalar (r : RatFunc K) : σ (algebraMap C₀ E (e r)) = (f) r := by
    rw [hσ]
    exact DFunLike.congr_fun hf r
  let mR := fun i => σ (graphRestrictedCovector p (Aₑ) M i)
  let sR := fun i => σ (graphRestrictedCovector p (Aₑ) S i)
  let bR := fun i : Fin 3 => σ (bE (p i.castSucc))
  let aR := fun i : Fin 3 => σ (aE (p i.castSucc))
  let Φ := fun i => (f) (rationalParameterDerivative K ((A) i))
  let W := LinearMap.ker (dotProductBilin κ κ Φ)
  have hbR : Φ ⬝ᵥ bR = 0 := by
    change (∑ i : Fin 3, algebraMap C₀ E (e (rationalParameterDerivative K ((A) i))) * bE (p i.castSucc)) = 0 at hbgraph
    simpa only [Φ, bR, map_sum, map_mul, map_zero, hscalar, dotProduct] using congrArg σ hbgraph
  have haR : Φ ⬝ᵥ aR = 0 := by
    change (∑ i : Fin 3, algebraMap C₀ E (e (rationalParameterDerivative K ((A) i))) * aE (p i.castSucc)) = 0 at hagraph
    simpa only [Φ, aR, map_sum, map_mul, map_zero, hscalar, dotProduct] using congrArg σ hagraph
  have hbW : bR ∈ W := hbR
  have haW : aR ∈ W := haR
  have hmbR : mR ⬝ᵥ bR = 1 := by
    simpa only [mR, bR, dotProduct, map_sum, map_mul, map_one] using congrArg σ hmb
  have hsbR : sR ⬝ᵥ bR = 0 := by
    simpa only [sR, bR, dotProduct, map_sum, map_mul, map_zero] using congrArg σ hsb
  have hmaR : mR ⬝ᵥ aR = 0 := by
    simpa only [mR, aR, dotProduct, map_sum, map_mul, map_zero] using congrArg σ hma
  have hsaR : sR ⬝ᵥ aR = 1 := by
    simpa only [sR, aR, dotProduct, map_sum, map_mul, map_one] using congrArg σ hsa
  have hfirst : Φ ≠ 0 := by
    intro hzero
    apply actual_closed_gauss_graph_gradient_derivative_ne_zero H I p hY h hh e hGauss
    funext i
    apply (g).injective
    change (g) ((f₀) (rationalParameterDerivative K ((A) i))) = (g) 0
    simpa only [Φ, AlgHom.comp_apply, map_zero, Pi.zero_apply] using congrFun hzero i
  have hdim : finrank κ W = 2 := nonzero_ternary_normal_kernel_finrank Φ hfirst
  have hpairR := ruling_form_pair_independent_of_specified_dual_values W mR sR bR aR
    hbW haW hmbR hsbR hmaR hsaR
  let v : Fin 3 → κ := fun i => z (some (p i.castSucc))
  have hvR : Φ ⬝ᵥ v = 0 := actual_full_boundary_closed_graph_ruling H I p hY h hh e κ
    hd hH hGauss c q hq z hz hpoint hz0
  have hvW : v ∈ W := hvR
  have hsv : sR ⬝ᵥ v = 0 := actual_normalized_boundary_annihilates_specified_simple_root_form
    H hrank I p hY h hh e κ hd1 hH hN hind hGauss c q k hc hq hk mR sR bR
      (fun i => halg _) (fun i => halg _) hbR hmbR hsbR rho hrho hprod hroot z hz hpoint hz0 j hj
  have hspan := ruling_coordinates_of_specified_dual_pair W hdim mR sR bR aR hpairR
    hbW haW hmbR hsbR hmaR hsaR v hvW
  let t := mR ⬝ᵥ v
  have hrep3 : v = t • bR := by
    funext i
    change v i = (mR ⬝ᵥ v) * bR i
    have hi := hspan i
    rw [hsv, mul_zero, add_zero] at hi
    exact hi.trans (mul_comm _ _)
  have hfull : (fun i : Fin 4 => z (some i)) ≠ 0 := by
    intro hzero
    have he := congrFun hzero j
    rw [hj] at he
    exact one_ne_zero he
  have hv0 : v ≠ 0 := actual_full_fiber_boundary_first_three_direction_ne_zero H p hY h c hc κ
    z hz hfull hpoint hz0
  have ht : t ≠ 0 := by
    intro hzero
    apply hv0
    rw [hrep3, hzero, zero_smul]
  have hzlinear : z (some (p 3)) = (fun i => (f) ((A) i)) ⬝ᵥ v := by
    have he := actual_full_fiber_boundary_graph_linear_equation H p hY h c hc κ z hz hpoint hz0
    simpa only [v, dotProduct, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
      closedGaussCoefficientGraphSlope_value] using he
  have hblinear := (actual_chosen_ruling_vector_constructs_original_graph_equations
    H I p hY h hh e E hH hd hind hGauss bE hbE).1
  have hblinearR : (fun i => σ (bE i)) (p 3) = (fun i => (f) ((A) i)) ⬝ᵥ bR := by
    simpa only [bR, dotProduct, map_sum, map_mul, hscalar] using congrArg σ hblinear
  have hbrec : graphBoundaryDirection p (fun i => (f) ((A) i)) bR = (fun i => σ (bE i)) :=
    graphBoundaryDirection_eq_full_vector p (fun i => (f) ((A) i)) (fun i => σ (bE i)) hblinearR
  have hrepFull0 := graph_boundary_direction_proportional_of_first_coordinates p
    (fun i => (f) ((A) i)) bR (RingHom.id κ) (fun i => z (some i)) t hzlinear hrep3
  have hrepFull : (fun i => z (some i)) = t • (fun i => σ (bE i)) := by
    simpa only [RingHom.id_apply, hbrec] using hrepFull0
  let beta := σ ((M (Fin.last 3))⁻¹)
  have hbeta : beta ≠ 0 := (map_ne_zero σ).mpr (inv_ne_zero hM)
  have haxisimage (i : Fin 4) :
      σ ((Fin.snoc (0 : Fin 3 → E) 1 : Fin 4 → E) i) =
        algebraMap (L) κ ((Fin.snoc (0 : Fin 3 → L) 1 : Fin 4 → L) i) := by
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Fin.snoc_last, map_one]
    · simp only [Fin.snoc_castSucc, Pi.zero_apply, map_zero]
  have hbimage : (fun i => σ (bE i)) = beta •
      (fun i => algebraMap (L) κ ((Fin.snoc (0 : Fin 3 → L) 1 : Fin 4 → L) i)) := by
    funext i
    rw [hbEq]
    change σ ((M (Fin.last 3))⁻¹ * (Fin.snoc (0 : Fin 3 → E) 1 : Fin 4 → E) i) =
      σ ((M (Fin.last 3))⁻¹) * algebraMap (L) κ ((Fin.snoc (0 : Fin 3 → L) 1 : Fin 4 → L) i)
    rw [map_mul, haxisimage]
  have hrepAxis : (fun i => z (some i)) = (t * beta) •
      (fun i => algebraMap (L) κ ((Fin.snoc (0 : Fin 3 → L) 1 : Fin 4 → L) i)) := by
    rw [hrepFull, hbimage, smul_smul]
  exact actual_boundary_multiple_fourth_axis_gives_original_vertex_membership
    (rationalCoordinate (K := K) (n := 4)) z hz hpoint hz0 (t * beta) (mul_ne_zero ht hbeta) hrepAxis

end DimensionFourDependence
