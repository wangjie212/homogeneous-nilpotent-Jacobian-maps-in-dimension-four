import DimensionFourDependence.DifferentiatedCurveSpan
import DimensionFourDependence.RationalGaussCurve
import DimensionFourDependence.ParametrizedNormalRadialExclusion

/-! # The actual Gauss curve has three independent successive normal covectors

Normalize the actual Gauss coordinate at its genuine pivot and use its
constructed rational parameter. If every first-derivative Wronskian
vanished, the exact constant-field argument would put all actual normal
coordinates in a fixed constant plane, forcing component dependence.
A nonzero Wronskian gives a genuine nonzero three-column jet determinant
and hence independence of the actual normal and its first two derivatives.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- A fixed constant affine span for the actual normalized normal
coordinates in any rational Gauss parameter forces original-field
component dependence. -/
theorem ImageRelationWitness.dependent_of_affine_rational_gauss_parameter
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (u : RatFunc K) (a b : Fin 4 → K)
    (hparam : ∀ i, e.symm (fullOutputCoordinate (K := K)
      (fun j => rationalImageNormal H I.equation j / rationalImageNormal H I.equation (imageNormalPivot H I)) i) =
      algebraMap K (RatFunc K) (a i) * u + algebraMap K (RatFunc K) (b i)) : ComponentsDependent H := by
  let ν := rationalImageNormal H I.equation
  let p := imageNormalPivot H I
  let M := projectiveRatioField (K := K) ν p
  let x : Fin 4 → M := fullOutputCoordinate (K := K) (fun i => ν i / ν p)
  let f : RatFunc K →ₐ[K] FractionRing (MvPolynomial (Fin 4) K) := M.val.comp e.toAlgHom
  have hp : ν p ≠ 0 := imageNormalPivot_ne_zero H I
  have hfcoord (i : Fin 4) : f (e.symm (x i)) = ν i / ν p := by
    change M.val (e (e.symm (x i))) = _
    rw [e.apply_symm_apply]
    rfl
  have hspan : finrank K (Submodule.span K (Set.range (imageRelationNormal H I.equation))) ≤ 2 := by
    apply polynomial_component_span_le_two_of_fraction_presentation (imageRelationNormal H I.equation)
      (ν p * f u) (ν p) a b
    intro i
    have he := congrArg f (hparam i)
    rw [hfcoord, map_add, map_mul, f.commutes, f.commutes] at he
    have hh := (div_eq_iff hp).mp he
    change ν i = algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (a i) * (ν p * f u) +
      algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (b i) * ν p
    rw [hh]
    ring
  exact dependent_of_normal_component_span_le_two H (imageRelationNormal H I.equation) hd hH
    I.normal_ne_zero (I.left_kernel H) hspan

/-- The actual one-dimensional Gauss image of a nonplanar homogeneous
map supplies three independent successive normal covectors in a
constructed rational parameter, with an actual nonzero jet minor.
No generic-independence or normal-span assumption is added. -/
theorem actual_gauss_curve_three_successive_covectors_independent
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1) :
    ∃ e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I),
      let w : Fin 4 → RatFunc K := fun i => e.symm (fullOutputCoordinate (K := K)
        (fun j => rationalImageNormal H I.equation j / rationalImageNormal H I.equation (imageNormalPivot H I)) i)
      ∃ i j : Fin 4, ((rationalParameterJetMatrix w).submatrix id ![imageNormalPivot H I, i, j]).det ≠ 0 ∧
        LinearIndependent (RatFunc K) (rationalParameterJetMatrix w).row := by
  obtain ⟨e⟩ := actual_gauss_curve_rational_function_field H I hGauss
  let M := projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)
  let x : Fin 4 → M := fullOutputCoordinate (K := K)
    (fun j => rationalImageNormal H I.equation j / rationalImageNormal H I.equation (imageNormalPivot H I))
  let w : Fin 4 → RatFunc K := fun i => e.symm (x i)
  have hcoord : x (imageNormalPivot H I) = 1 := by
    apply Subtype.ext
    exact div_self (imageNormalPivot_ne_zero H I)
  have hw : w (imageNormalPivot H I) = 1 := by
    change e.symm _ = 1
    rw [hcoord, map_one]
  have hex : ∃ i j, rationalParameterDerivative K (w i) * rationalParameterDerivative K (rationalParameterDerivative K (w j)) -
      rationalParameterDerivative K (w j) * rationalParameterDerivative K (rationalParameterDerivative K (w i)) ≠ 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨u, hu⟩ := rational_parameter_derivative_wronskians_zero_affine_span w hn
    choose a b he using hu
    exact hind (I.dependent_of_affine_rational_gauss_parameter H hd hH e u a b he)
  obtain ⟨i, j, hij⟩ := hex
  have hdet : ((rationalParameterJetMatrix w).submatrix id ![imageNormalPivot H I, i, j]).det ≠ 0 := by
    rw [rationalParameterJetMatrix_det_normalized_column w _ i j hw]
    exact hij
  exact ⟨e, i, j, hdet, three_rows_independent_of_column_minor (rationalParameterJetMatrix w) _ hdet⟩

end DimensionFourDependence
