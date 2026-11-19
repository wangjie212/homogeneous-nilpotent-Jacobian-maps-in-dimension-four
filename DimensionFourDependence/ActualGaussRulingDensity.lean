import DimensionFourDependence.GaussFiberDimension
import DimensionFourDependence.RulingGenericPointDensity

/-! # The actual generic Gauss fiber fills its actual ruling

Transport the two actual normal covectors into the actual Gauss function
field. Their kernel is two-dimensional, the actual output point belongs
to its coefficient extension, and that point retains transcendence
degree two. Hence every polynomial relation over the actual Gauss field
vanishes on the entire ruling. In particular the ruling lies on the
original image equation after extending coefficients to the Gauss field.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- The two ruling equations over the actual Gauss field itself. -/
noncomputable def actualGaussRulingMatrix
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) :
    Matrix (Fin 2) (Fin 4) (projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) :=
  (normalRulingMatrix (rationalParameterDerivative K) (gaussParameterNormal H I e)).map e

/-- The genuine actual image point belongs to the coefficient extension
of the ruling equations over the actual Gauss field. -/
theorem ImageRelationWitness.output_mem_actual_gauss_ruling
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hH : IsHomogMap H d) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) :
    (actualGaussRulingMatrix H I e).map
      (algebraMap (projectiveRatioField (K := K) (rationalImageNormal H I.equation)
        (imageNormalPivot H I)) (FractionRing (MvPolynomial (Fin 4) K))) *ᵥ
      (fun i => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H i)) = 0 := by
  exact I.output_mem_parameter_ruling H hd hH e

omit [CharZero K] in
/-- Three independent successive actual covectors give a
two-dimensional ruling over the actual Gauss field. -/
theorem actualGaussRulingMatrix_kernel_finrank
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (hLI : LinearIndependent (RatFunc K)
      (rationalParameterJetMatrix (gaussParameterNormal H I e)).row) :
    finrank (projectiveRatioField (K := K) (rationalImageNormal H I.equation)
      (imageNormalPivot H I)) (LinearMap.ker (actualGaussRulingMatrix H I e).toLin') = 2 := by
  let w := gaussParameterNormal H I e
  have hpair : LinearIndependent (RatFunc K) ![w, fun i => rationalParameterDerivative K (w i)] := by
    have hh := hLI.comp (Fin.castSucc : Fin 2 → Fin 3) (Fin.castSucc_injective 2)
    convert hh using 1
    funext r i
    fin_cases r <;> rfl
  have hrows : LinearIndependent
      (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
      (actualGaussRulingMatrix H I e).row := by
    convert independent_covector_pair_after_field_map e.toRingHom w
      (fun i => rationalParameterDerivative K (w i)) hpair using 1
    funext r i
    fin_cases r <;> rfl
  have hr : (actualGaussRulingMatrix H I e).rank = 2 := hrows.rank_matrix
  have he := LinearMap.finrank_range_add_finrank_ker (actualGaussRulingMatrix H I e).toLin'
  have hrr : finrank
      (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
      (LinearMap.range (actualGaussRulingMatrix H I e).toLin') = 2 := hr
  simp only [Module.finrank_pi, Fintype.card_fin] at he
  omega

/-- The actual rank-three homogeneous image with one-dimensional
nonplanar Gauss image is polynomially dense in its actual ruling over
the actual Gauss field. No ruling-density hypothesis is added. -/
theorem actual_gauss_fiber_ruling_polynomial_density
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 1) :
    ∃ e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I),
      let M := projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)
      let A := actualGaussRulingMatrix H I e
      finrank M (LinearMap.ker A.toLin') = 2 ∧
      ∀ P : MvPolynomial (Fin 4) M,
        aeval (fun i => algebraMap (MvPolynomial (Fin 4) K)
          (FractionRing (MvPolynomial (Fin 4) K)) (H i)) P = 0 →
          ∀ x ∈ LinearMap.ker A.toLin', aeval x P = 0 := by
  obtain ⟨e, _, _, _, hLI⟩ := actual_gauss_curve_three_successive_covectors_independent H hd hH hind I hGauss
  have hA := actualGaussRulingMatrix_kernel_finrank H I e hLI
  exact ⟨e, hA, two_dimensional_matrix_kernel_generic_point_density
    (actualGaussRulingMatrix H I e) hA _ (I.output_mem_actual_gauss_ruling H hd hH e)
    (actual_gauss_fiber_output_trdeg_two H hrank I hGauss)⟩

/-- The actual ruling lies on the original image hypersurface, with
coefficients transported to the actual Gauss field. -/
theorem actual_gauss_ruling_contained_image_equation
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 1) :
    ∃ e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I),
      let M := projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)
      finrank M (LinearMap.ker (actualGaussRulingMatrix H I e).toLin') = 2 ∧
      ∀ x ∈ LinearMap.ker (actualGaussRulingMatrix H I e).toLin',
        aeval x (MvPolynomial.map (algebraMap K M) I.equation) = 0 := by
  obtain ⟨e, hA, hdense⟩ := actual_gauss_fiber_ruling_polynomial_density H hd hH hrank hind I hGauss
  refine ⟨e, hA, hdense _ ?_⟩
  rw [aeval_map_algebra_extension, ← aeval_polynomial_to_fraction, I.vanishing, map_zero]

end DimensionFourDependence
