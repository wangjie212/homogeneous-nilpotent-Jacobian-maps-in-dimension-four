import DimensionFourDependence.ActualBoundaryRulingParameter
import DimensionFourDependence.ClosedGaussCoefficientRealization
import DimensionFourDependence.ParametricGraphHessian

/-! # Actual graph equations in the original birational Gauss parameter

The graph gradient already generates the original Gauss field. It can
therefore be written in the original parameter before passing to any
finite closed cover. The actual Euler equation and coefficient partials
derive its ruling equation and rank-one Hessian in that parameter.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

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

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "M" => projectiveRatioField (K := K)
  (rationalImageNormal H I.equation) (imageNormalPivot H I)

variable (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
  (rationalImageNormal H I.equation) (imageNormalPivot H I))

/-- The original birational Gauss parameter in the actual coefficient
field, with exactly its original-source realization. -/
noncomputable def originalGaussCoefficientParameterHom : RatFunc K →ₐ[K] (L) :=
  (actualChartGaussFieldHom H hrank p hY I).comp e.toAlgHom

theorem originalGaussCoefficientParameterHom_source_value (r : RatFunc K) :
    (originalGaussCoefficientParameterHom H hrank I p hY e r : S₀) =
      gaussParameterSourceHom H I e r := rfl

variable
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))

/-- The actual graph gradient as rational functions of the original
Gauss parameter, without an auxiliary finite-cover parameter. -/
noncomputable def originalGaussCoefficientGraphSlope (i : Fin 3) : RatFunc K :=
  e.symm ⟨(coefficientPartial (Y) hY i h : S₀), by
    rw [actual_gauss_field_eq_graph_gradient_adjoin H I p hY h hh]
    exact IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩

local notation "f₀" => originalGaussCoefficientParameterHom H hrank I p hY e
local notation "A₀" => originalGaussCoefficientGraphSlope H I p hY e h hh

include hh

/-- The original-parameter slope has the original actual coefficient
partial as its value. -/
theorem originalGaussCoefficientGraphSlope_value (i : Fin 3) :
    (f₀) ((A₀) i) = coefficientPartial (Y) hY i h := by
  apply Subtype.ext
  rw [originalGaussCoefficientParameterHom_source_value]
  unfold originalGaussCoefficientGraphSlope
  change (e (e.symm _) : S₀) = _
  rw [e.apply_symm_apply]

omit h hh in
/-- The original parameter has a nonzero actual coefficient partial,
derived from its original-source transcendence. -/
theorem originalGaussCoefficientParameterHom_partial_ne_zero :
    ∃ j, coefficientPartial (Y) hY j ((f₀) RatFunc.X) ≠ 0 := by
  apply coefficient_partials_nonzero_of_transcendental (Y) hY
  rw [originalGaussCoefficientParameterHom_source_value]
  exact gaussParameterSourceHom_X_transcendental H I e

variable (hGauss : gaussImageDimension H I = 1)

include hGauss

/-- The actual original-parameter graph-gradient derivative is nonzero. -/
theorem original_gauss_graph_gradient_derivative_ne_zero :
    (fun i => (f₀) (rationalParameterDerivative K ((A₀) i))) ≠ 0 := by
  apply parametric_graph_gradient_derivative_ne_zero (f₀) (coefficientPartial (Y) hY) (A₀) h
    (fun i => (originalGaussCoefficientGraphSlope_value H hrank I p hY e h hh i).symm)
  intro hz
  have he := I.gauss_image_dimension_eq_hessian H p hY h hh
  change derivationHessian (coefficientPartial (Y) hY) h = 0 at hz
  change gaussImageDimension H I = (derivationHessian (coefficientPartial (Y) hY) h).rank at he
  rw [hz, Matrix.rank_zero, hGauss] at he
  exact one_ne_zero he

variable {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)

include hd hH

omit hGauss in
/-- The actual Euler identity gives the ruling equation in the
original birational Gauss parameter. -/
theorem original_gauss_graph_ruling_equation :
    (fun i => (f₀) (rationalParameterDerivative K ((A₀) i))) ⬝ᵥ
      coefficientCoordinate (K := K) (Y) = 0 :=
  parametric_graph_ruling_equation_of_euler (f₀) (coefficientPartial (Y) hY)
    (coefficientCoordinate (K := K) (Y)) (coefficientPartial_coordinate (Y) hY) (A₀) h
    (fun i => (originalGaussCoefficientGraphSlope_value H hrank I p hY e h hh i).symm)
    (homogeneous_last_output_euler H hd hH p hY h hh)
    (originalGaussCoefficientParameterHom_partial_ne_zero H hrank I p hY e)

/-- The original-parameter ruling denominator is nonzero. -/
theorem original_gauss_graph_denominator_ne_zero :
    parametricRulingDenominator (f₀) (A₀) (coefficientCoordinate (K := K) (Y)) ≠ 0 :=
  parametric_ruling_denominator_ne_zero (f₀) (coefficientPartial (Y) hY)
    (coefficientCoordinate (K := K) (Y)) (coefficientPartial_coordinate (Y) hY) (A₀)
    (original_gauss_graph_ruling_equation H hrank I p hY e h hh hd hH)
    (original_gauss_graph_gradient_derivative_ne_zero H hrank I p hY e h hh hGauss)

/-- The actual rank-one graph Hessian formula uses the original
Gauss parameter itself, with no parameter-change assumption. -/
theorem original_gauss_graph_hessian_formula (i j : Fin 3) :
    coefficientHessian (Y) hY h i j =
      -((f₀) (rationalParameterDerivative K ((A₀) i)) *
        (f₀) (rationalParameterDerivative K ((A₀) j))) /
        parametricRulingDenominator (f₀) (A₀) (coefficientCoordinate (K := K) (Y)) :=
  parametric_graph_hessian_formula (f₀) (coefficientPartial (Y) hY)
    (coefficientCoordinate (K := K) (Y)) (coefficientPartial_coordinate (Y) hY) (A₀)
    (original_gauss_graph_ruling_equation H hrank I p hY e h hh hd hH)
    (original_gauss_graph_gradient_derivative_ne_zero H hrank I p hY e h hh hGauss)
    h (fun k => (originalGaussCoefficientGraphSlope_value H hrank I p hY e h hh k).symm) i j

end DimensionFourDependence
