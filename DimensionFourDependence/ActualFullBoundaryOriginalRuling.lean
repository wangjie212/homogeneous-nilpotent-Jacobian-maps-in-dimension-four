import DimensionFourDependence.GraphNormalParameterRuling
import DimensionFourDependence.ProjectiveClosureLeadingEquations
import DimensionFourDependence.ParametricGraphBaseChange

/-! # The actual full-coordinate boundary lies on the original Gauss ruling

The first invariant gives the full boundary's graph hyperplane equation.
The quadratic invariant and the original-parameter Hessian formula give
the graph ruling equation. The actual normal graph identity then puts
the full four-coordinate direction in the original normal ruling.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "x" => rationalCoordinate (K := K) (n := 4)

include hY

/-- The original first invariant gives the actual full boundary's
linear graph equation at every extension-field point at infinity. -/
theorem actual_full_fiber_boundary_graph_linear_equation
    (h c : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (κ : Type u) [Field κ] [Algebra (L) κ]
    (z : Option (Fin 4) → κ) (hz : z ≠ 0)
    (hboundary : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (x))
    (hz0 : z none = 0) :
    z (some (p 3)) = ∑ i : Fin 3,
      algebraMap (L) κ (coefficientPartial (Y) hY i h) * z (some (p i.castSucc)) := by
  let T : MvPolynomial (Option (Fin 4)) (L) :=
    X (some (p 3)) - (∑ i : Fin 3, C (coefficientPartial (Y) hY i h) * X (some (p i.castSucc))) -
      C c * X none
  have hsum : (∑ i : Fin 3, C (coefficientPartial (Y) hY i h) * X (some (p i.castSucc))).IsHomogeneous 1 := by
    apply IsHomogeneous.sum
    intro i _
    exact isHomogeneous_C_mul_X _ _
  have hT : T.IsHomogeneous 1 :=
    ((isHomogeneous_X (R := L) (some (p 3))).sub hsum).sub (isHomogeneous_C_mul_X _ _)
  have hvan : T ∈ projectiveConeIdeal («L» := L) (x) := by
    apply (projectiveConeIdeal_mem_of_isHomogeneous (x) hT).mpr
    simp only [T, map_sub, map_sum, map_mul, aeval_C, aeval_X, Option.elim_some, Option.elim_none, mul_one]
    change (x) (p 3) - (∑ i : Fin 3, (coefficientPartial (Y) hY i h : S₀) * (x) (p i.castSucc)) -
      (c : S₀) = 0
    exact sub_eq_zero.mpr hc.symm
  have he := projectiveClosureSet_extension_coordinate_equation (x) z hz hboundary hT hvan
  simp only [T, map_sub, map_sum, map_mul, aeval_C, aeval_X, hz0, mul_zero, sub_zero] at he
  exact sub_eq_zero.mp he

variable (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))

local notation "f₀" => originalGaussCoefficientParameterHom H hrank I p hY e
local notation "A₀" => originalGaussCoefficientGraphSlope H I p hY e h hh

include hh

/-- The actual quadratic invariant puts every full boundary point at
infinity on the graph ruling in the original Gauss parameter. -/
theorem actual_full_fiber_boundary_original_graph_ruling
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hGauss : gaussImageDimension H I = 1)
    (c q : L) (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (κ : Type u) [Field κ] [Algebra (L) κ]
    (z : Option (Fin 4) → κ) (hz : z ≠ 0)
    (hboundary : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (x))
    (hz0 : z none = 0) :
    (fun i => algebraMap (L) κ ((f₀) (rationalParameterDerivative K ((A₀) i)))) ⬝ᵥ
      (fun i => z (some (p i.castSucc))) = 0 := by
  let : CharZero (L) := charZero_of_injective_algebraMap (algebraMap K (L)).injective
  have he := projective_fiber_closure_quadratic_isotropic (x) z hz hboundary hz0
    (fun i : Fin 3 => p i.castSucc) (coefficientGradient (Y) hY c) (coefficientHessian (Y) hY h) q
    (quadraticFiberEquation_aeval_zero p (Y) hY h c q hq)
  have hB : (coefficientHessian (Y) hY h).map (algebraMap (L) κ) = fun i j =>
      -(algebraMap (L) κ ((f₀) (rationalParameterDerivative K ((A₀) i))) *
        algebraMap (L) κ ((f₀) (rationalParameterDerivative K ((A₀) j)))) /
          algebraMap (L) κ (parametricRulingDenominator (f₀) (A₀) (coefficientCoordinate (K := K) (Y))) := by
    ext i j
    rw [Matrix.map_apply, original_gauss_graph_hessian_formula H hrank I p hY e h hh hGauss hd hH]
    simp only [map_div₀, map_neg, map_mul]
  rw [hB] at he
  exact (rank_one_quotient_isotropic_iff _ _ _
    ((map_ne_zero (algebraMap (L) κ)).mpr
      (original_gauss_graph_denominator_ne_zero H hrank I p hY e h hh hGauss hd hH))).mp he

/-- Both original invariant equations put the entire actual
four-coordinate boundary direction in the actual original Gauss ruling.
No ruling membership or finite-cover parameter comparison is assumed. -/
theorem actual_full_fiber_boundary_mem_original_gauss_ruling
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hGauss : gaussImageDimension H I = 1)
    (c q : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (κ : Type u) [Field κ] [Algebra (L) κ]
    (z : Option (Fin 4) → κ) (hz : z ≠ 0)
    (hboundary : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (x))
    (hz0 : z none = 0) :
    (actualGaussRulingMatrix H I e).map
      ((algebraMap (L) κ).comp (actualChartGaussFieldHom H hrank p hY I).toRingHom) *ᵥ
        (fun i => z (some i)) = 0 := by
  let f : RatFunc K →+* κ := (algebraMap (L) κ).comp (f₀).toRingHom
  have hlinear : z (some (p 3)) = ∑ i : Fin 3, f ((A₀) i) * z (some (p i.castSucc)) := by
    change z (some (p 3)) = ∑ i : Fin 3,
      algebraMap (L) κ ((f₀) ((A₀) i)) * z (some (p i.castSucc))
    simp only [originalGaussCoefficientGraphSlope_value]
    exact actual_full_fiber_boundary_graph_linear_equation H p hY h c hc κ z hz hboundary hz0
  have hruling := actual_full_fiber_boundary_original_graph_ruling H hrank p hY I e h hh
    hd hH hGauss c q hq κ z hz hboundary hz0
  exact normal_parameter_ruling_of_graph_equations (rationalParameterDerivative K) (gaussParameterNormal H I e)
    (A₀) p (original_gauss_normal_graph_coordinate_relation H hrank I p hY e h hh) f
    (fun i => z (some i)) hlinear hruling

end DimensionFourDependence
