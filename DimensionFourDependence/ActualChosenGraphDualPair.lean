import DimensionFourDependence.ActualRootCharacteristicComparison
import DimensionFourDependence.GraphRulingCovectorProjection
import DimensionFourDependence.RulingCoordinateBasis

/-! # The original chosen ruling constructs its graph dual pair -/

namespace DimensionFourDependence

open Matrix Module MvPolynomial

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

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
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]

local notation "C₀" => closedGaussParameterField H I
local notation "A" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "A꜀" => (fun i => e ((A) i))
local notation "Aₑ" => (fun i => algebraMap C₀ E (e ((A) i)))

/-- The actual graph ruling over the given original finite
coefficient field, using the original closed-cover parameter. -/
noncomputable def extendedClosedGaussGraphRuling : Submodule E (Fin 3 → E) :=
  LinearMap.ker (dotProductBilin E E
    (fun i => algebraMap C₀ E (e (rationalParameterDerivative K ((A) i)))))

variable {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "e₀" => actualGaussRulingParameterChoice H I hH hd hind hGauss
local notation "W₀" => LinearMap.ker (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin'
local notation "Wg" => extendedClosedGaussGraphRuling H I p hY h hh e E

/-- Every original chosen-ruling vector has the exact graph linear
equation and projects into the actual graph ruling. The change from
the original Gauss parameter to the closed-cover parameter and its
normal pivot are both derived from the original map. -/
theorem actual_chosen_ruling_vector_constructs_original_graph_equations
    (b : Fin 4 → E) (hb : b ∈ W₀) :
    b (p 3) = ∑ i : Fin 3, (Aₑ) i * b (p i.castSucc) ∧
      (fun i => b (p i.castSucc)) ∈ (Wg) := by
  let f := closedGaussOriginalParameterHom H I (e₀)
  let D := closedGaussCoverDerivation H I e
  let a := actualClosedGaussNormalCovector H I e (p 3)
  have hgraph : ∀ i, f (gaussParameterNormal H I (e₀) i) = a * parameterGraphNormal p (A꜀) i :=
    closedGaussOriginalParameterHom_graph_normal H I p hY h hh e (e₀)
  have hb' : (normalRulingMatrix (rationalParameterDerivative K) (gaussParameterNormal H I (e₀))).map
      ((algebraMap C₀ E).comp f.toRingHom) *ᵥ b = 0 := hb
  have he := original_normal_ruling_constructs_graph_projection_equations f D
    (gaussParameterNormal H I (e₀)) p (A꜀) a hgraph
    (actualClosedGaussNormalCovector_graph_pivot_ne_zero H I p hY h hh e)
    (algebraMap C₀ E) b hb'
  have hD (i : Fin 3) : D ((A꜀) i) = e (rationalParameterDerivative K ((A) i)) := by
    change e (rationalParameterDerivative K (e.symm (e ((A) i)))) = _
    rw [e.symm_apply_apply]
  refine ⟨he.1, ?_⟩
  change (∑ i : Fin 3, algebraMap C₀ E (e (rationalParameterDerivative K ((A) i))) * b (p i.castSucc)) = 0
  simpa only [hD] using he.2

/-- Independent original ruling forms construct one original dual
pair whose graph projections retain all four dual values and prove
independence of the graph-restricted forms on the actual graph ruling. -/
theorem actual_chosen_ruling_independent_forms_construct_original_graph_dual_pair
    (m s : Fin 4 → E)
    (hpair : LinearIndependent E ![rulingFormRestriction W₀ m, rulingFormRestriction W₀ s]) :
    let m₃ := graphRestrictedCovector p (Aₑ) m
    let s₃ := graphRestrictedCovector p (Aₑ) s
    ∃ b a : Fin 4 → E, b ∈ W₀ ∧ a ∈ W₀ ∧
      (fun i => b (p i.castSucc)) ∈ (Wg) ∧ (fun i => a (p i.castSucc)) ∈ (Wg) ∧
      m₃ ⬝ᵥ (fun i => b (p i.castSucc)) = 1 ∧
      s₃ ⬝ᵥ (fun i => b (p i.castSucc)) = 0 ∧
      m₃ ⬝ᵥ (fun i => a (p i.castSucc)) = 0 ∧
      s₃ ⬝ᵥ (fun i => a (p i.castSucc)) = 1 ∧
      LinearIndependent E ![rulingFormRestriction (Wg) m₃, rulingFormRestriction (Wg) s₃] := by
  obtain ⟨b, a, _hLI, hb, ha, hmb, hsb, hma, hsa, _hspan⟩ :=
    two_dimensional_ruling_coordinate_basis W₀
      (extendedClosedGaussChosenRulingMatrix_kernel_finrank H I E hH hd hind hGauss) m s hpair
  obtain ⟨hblinear, hbgraph⟩ := actual_chosen_ruling_vector_constructs_original_graph_equations
    H I p hY h hh e E hH hd hind hGauss b hb
  obtain ⟨halinear, hagraph⟩ := actual_chosen_ruling_vector_constructs_original_graph_equations
    H I p hY h hh e E hH hd hind hGauss a ha
  have hmb' := (graphRestrictedCovector_pairing p (Aₑ) m b hblinear).trans hmb
  have hsb' := (graphRestrictedCovector_pairing p (Aₑ) s b hblinear).trans hsb
  have hma' := (graphRestrictedCovector_pairing p (Aₑ) m a halinear).trans hma
  have hsa' := (graphRestrictedCovector_pairing p (Aₑ) s a halinear).trans hsa
  exact ⟨b, a, hb, ha, hbgraph, hagraph, hmb', hsb', hma', hsa',
    ruling_form_pair_independent_of_specified_dual_values (Wg) _ _ _ _
      hbgraph hagraph hmb' hsb' hma' hsa'⟩

end DimensionFourDependence
