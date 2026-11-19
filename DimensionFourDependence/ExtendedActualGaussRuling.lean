import DimensionFourDependence.ExtendedParameterOutputRelations
import DimensionFourDependence.ActualGaussRulingDensity
import DimensionFourDependence.RulingFormCoordinateSpan

/-! # The actual extended Gauss ruling contains the native component values and supplies their coordinates -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module AlgebraicGeometry

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "G₀" => projectiveRatioField (K := K)
  (rationalImageNormal H I.equation) (imageNormalPivot H I)
local notation "C₀" => closedGaussParameterField H I
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance extendedActualGaussRulingIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance extendedActualGaussRulingAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual Gauss ruling over the actual extended parameter field,
retaining its original normal covectors and four original coordinates. -/
noncomputable def extendedClosedGaussRulingMatrix (e₀ : RatFunc K ≃ₐ[K] G₀) : Matrix (Fin 2) (Fin 4) E :=
  (actualGaussRulingMatrix H I e₀).map ((algebraMap C₀ E).comp (algebraMap G₀ C₀))

/-- The actual original component values on the normalized pencil
belong to the scalar extension of the actual ruling. Its annihilation
equations are derived from the original output point, not assumed on N. -/
theorem extendedClosedGauss_native_output_mem_actual_ruling
    (hd : 0 < d) (e₀ : RatFunc K ≃ₐ[K] G₀) :
    (extendedClosedGaussRulingMatrix H I E e₀).map (algebraMap E (N).functionField) *ᵥ
      (fun i => aeval w (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i))) = 0 := by
  have hsource := I.output_mem_actual_gauss_ruling H hd hH e₀
  funext r
  let c : Fin 4 → C₀ := fun i => algebraMap G₀ C₀ (actualGaussRulingMatrix H I e₀ r i)
  have hrel : ∑ i, algebraMap C₀ (FractionRing (MvPolynomial (Fin 4) K)) (c i) *
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i) = 0 := by
    have hr := congrFun hsource r
    simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, c,
      ← IsScalarTower.algebraMap_apply G₀ C₀ (FractionRing (MvPolynomial (Fin 4) K))] using hr
  exact extendedClosedGauss_original_output_covector_relation H I E hH e c hrel

omit [CharZero K] [Algebra.IsAlgebraic (closedGaussParameterField H I) E] in
/-- The original independent successive normal covectors give a
two-dimensional actual ruling after the actual coefficient extension. -/
theorem extendedClosedGaussRulingMatrix_kernel_finrank
    (e₀ : RatFunc K ≃ₐ[K] G₀)
    (hLI : LinearIndependent (RatFunc K)
      (rationalParameterJetMatrix (gaussParameterNormal H I e₀)).row) :
    finrank E (LinearMap.ker (extendedClosedGaussRulingMatrix H I E e₀).toLin') = 2 := by
  let v := gaussParameterNormal H I e₀
  have hpair : LinearIndependent (RatFunc K) ![v, fun i => rationalParameterDerivative K (v i)] := by
    have hh := hLI.comp (Fin.castSucc : Fin 2 → Fin 3) (Fin.castSucc_injective 2)
    convert hh using 1
    funext r i
    fin_cases r <;> rfl
  have hrows : LinearIndependent E (extendedClosedGaussRulingMatrix H I E e₀).row := by
    let ι := ((algebraMap C₀ E).comp (algebraMap G₀ C₀)).comp e₀.toRingHom
    convert independent_covector_pair_after_field_map ι v
      (fun i => rationalParameterDerivative K (v i)) hpair using 1
    funext r i
    fin_cases r <;> rfl
  have hr : (extendedClosedGaussRulingMatrix H I E e₀).rank = 2 := hrows.rank_matrix
  have he := LinearMap.finrank_range_add_finrank_ker (extendedClosedGaussRulingMatrix H I E e₀).toLin'
  have hrr : finrank E (LinearMap.range (extendedClosedGaussRulingMatrix H I E e₀).toLin') = 2 := hr
  simp only [Module.finrank_pi, Fintype.card_fin] at he
  omega

/-- Two independent actual ruling forms supply actual coefficient
expressions for every original native component in terms of the two
original output-linear sections. No component-span equations are inputs. -/
theorem extendedClosedGauss_native_output_span_of_independent_ruling_forms
    (hd : 0 < d) (e₀ : RatFunc K ≃ₐ[K] G₀)
    (hLI : LinearIndependent (RatFunc K)
      (rationalParameterJetMatrix (gaussParameterNormal H I e₀)).row)
    (cS cN : Fin 4 → E)
    (hpair : LinearIndependent E
      ![rulingFormRestriction (LinearMap.ker (extendedClosedGaussRulingMatrix H I E e₀).toLin') cS,
        rulingFormRestriction (LinearMap.ker (extendedClosedGaussRulingMatrix H I E e₀).toLin') cN]) :
    ∃ bS bN : Fin 4 → E, ∀ i,
      aeval w (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i)) =
        algebraMap E (N).functionField (bS i) * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS) +
          algebraMap E (N).functionField (bN i) * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) := by
  obtain ⟨bS, bN, hcoord⟩ := two_dimensional_matrix_kernel_coordinate_form_span_after_extension
    (E := (N).functionField) (extendedClosedGaussRulingMatrix H I E e₀)
    (extendedClosedGaussRulingMatrix_kernel_finrank H I E e₀ hLI) cS cN hpair
  refine ⟨bS, bN, fun i => ?_⟩
  have hi := hcoord _ (extendedClosedGauss_native_output_mem_actual_ruling H I E hH e hd e₀) i
  have hs : ((fun j => algebraMap E (N).functionField (cS j)) ⬝ᵥ
      (fun j => aeval w (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H j)))) =
        aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS) :=
    (extendedClosedGaussOutputLinearPolynomial_value H I E hH e cS).symm
  have hn : ((fun j => algebraMap E (N).functionField (cN j)) ⬝ᵥ
      (fun j => aeval w (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H j)))) =
        aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) :=
    (extendedClosedGaussOutputLinearPolynomial_value H I E hH e cN).symm
  rwa [hs, hn] at hi

/-- The original nonplanar homogeneous map with Gauss dimension one
constructs an actual two-dimensional ruling over every given algebraic
extension of its closed parameter field. Every pair of independent forms
on it gives all native original component-span coefficients. -/
theorem exists_extendedClosedGauss_actual_ruling_and_component_spans
    (hd : 0 < d) (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1) :
    ∃ e₀ : RatFunc K ≃ₐ[K] G₀,
      finrank E (LinearMap.ker (extendedClosedGaussRulingMatrix H I E e₀).toLin') = 2 ∧
      ∀ cS cN : Fin 4 → E, LinearIndependent E
        ![rulingFormRestriction (LinearMap.ker (extendedClosedGaussRulingMatrix H I E e₀).toLin') cS,
          rulingFormRestriction (LinearMap.ker (extendedClosedGaussRulingMatrix H I E e₀).toLin') cN] →
        ∃ bS bN : Fin 4 → E, ∀ i,
          aeval w (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i)) =
            algebraMap E (N).functionField (bS i) * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS) +
              algebraMap E (N).functionField (bN i) * aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) := by
  obtain ⟨e₀, _i, _j, _hminor, hLI⟩ :=
    actual_gauss_curve_three_successive_covectors_independent H hd hH hind I hGauss
  exact ⟨e₀, extendedClosedGaussRulingMatrix_kernel_finrank H I E e₀ hLI,
    fun cS cN hpair => extendedClosedGauss_native_output_span_of_independent_ruling_forms
      H I E hH e hd e₀ hLI cS cN hpair⟩

end DimensionFourDependence
