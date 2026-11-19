import DimensionFourDependence.SpecifiedGraphDualTransport
import DimensionFourDependence.FixedVertexScaledDualOutputBasis
import DimensionFourDependence.FixedVertexRootNumerator

/-! # The original canonical numerator supplies the simple-root graph factor and independent forms -/

namespace DimensionFourDependence

open Matrix Module MvPolynomial AlgebraicGeometry

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
local notation "Aₑ" => (fun i => algebraMap C₀ E (e ((A) i)))
local notation "a₀" => actualClosedGaussNormalCovector H I e (p 3)
local notation "n꜀" => closedGaussCanonicalRootNumerator H I p hY h hh e E

/-- The original canonical numerator restricts to exactly the
second graph-gradient derivative divided by the original normal pivot. -/
theorem canonical_root_numerator_graph_restriction :
    graphRestrictedCovector p (Aₑ) (n꜀) =
      fun i => (algebraMap C₀ E (a₀))⁻¹ *
        algebraMap C₀ E (e (rationalParameterDerivative K (rationalParameterDerivative K ((A) i)))) := by
  funext i
  simp only [graphRestrictedCovector, closedGaussCanonicalRootNumerator, Pi.smul_apply,
    smul_eq_mul, Function.comp_apply, Equiv.symm_apply_apply, Fin.snoc_castSucc,
    show (3 : Fin 4) = Fin.last 3 from rfl, Fin.snoc_last, mul_zero, zero_mul, add_zero,
    closedGaussRootNumeratorCoefficient, actualClosedGaussNormalCovector]

variable {B : Type u} [Field B] [Algebra K B]

/-- With the original canonical numerator, the scaled-plane root
rho=u L gives the exact graph factor n(Y)c=m(Y)rho for m=u^{-1}n.
The pivot and coefficient maps are the specified original ones. -/
theorem canonical_scaled_plane_root_constructs_original_graph_factor
    (g : C₀ →ₐ[K] B) (σ : E →+* B)
    (hσ : ∀ c : C₀, σ (algebraMap C₀ E c) = g c)
    (u : E) (hu : u ≠ 0) (y : Fin 3 → B) (rho c : B)
    (hrho : rho = σ u * g (a₀) * c) :
    parametricRulingDenominator (g.comp e.toAlgHom) (A) y * c =
      ((σ ∘ graphRestrictedCovector p (Aₑ) (u⁻¹ • (n꜀))) ⬝ᵥ y) * rho := by
  have hscale (i : Fin 3) : graphRestrictedCovector p (Aₑ) (u⁻¹ • (n꜀)) i =
      u⁻¹ * graphRestrictedCovector p (Aₑ) (n꜀) i := by
    simp only [graphRestrictedCovector, Pi.smul_apply, smul_eq_mul]
    ring
  have hm (i : Fin 3) : (σ ∘ graphRestrictedCovector p (Aₑ) (u⁻¹ • (n꜀))) i =
      (σ u)⁻¹ * (g (a₀))⁻¹ *
        (g.comp e.toAlgHom) (rationalParameterDerivative K (rationalParameterDerivative K ((A) i))) := by
    change σ (graphRestrictedCovector p (Aₑ) (u⁻¹ • (n꜀)) i) = _
    rw [hscale, congrFun (canonical_root_numerator_graph_restriction H I p hY h hh e E) i]
    simp only [map_mul, map_inv₀, hσ, AlgHom.comp_apply]
    change (σ u)⁻¹ * ((g (a₀))⁻¹ * g (e _)) = (σ u)⁻¹ * (g (a₀))⁻¹ * g (e _)
    exact (mul_assoc _ _ _).symm
  have hdot : (σ ∘ graphRestrictedCovector p (Aₑ) (u⁻¹ • (n꜀))) ⬝ᵥ y =
      (σ u)⁻¹ * (g (a₀))⁻¹ * parametricRulingDenominator (g.comp e.toAlgHom) (A) y := by
    simp only [dotProduct, hm, parametricRulingDenominator, Finset.mul_sum, mul_assoc]
  have hu' : σ u ≠ 0 := (map_ne_zero σ).mpr hu
  have ha' : g (a₀) ≠ 0 := (map_ne_zero g).mpr
    (actualClosedGaussNormalCovector_graph_pivot_ne_zero H I p hY h hh e)
  rw [hdot, hrho]
  field_simp [hu', ha']
  <;> ring

variable [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "W₀" => LinearMap.ker (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin'

local instance canonicalGraphRootFactorIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance canonicalGraphRootFactorAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

include hvertex

/-- The actual fixed vertex, nonzero canonical numerator and
nonzero plane scale construct independence of the exact forms m=u^{-1}n
and s on the original chosen ruling. This is the Section 4.3 pair needed
for the proportional-numerator scaled-plane branch. -/
theorem fixed_vertex_canonical_scaled_plane_forms_independent_on_actual_ruling
    (s : Fin 4 → E) (hs : s (Fin.last 3) ≠ 0)
    (hn : aeval (w) ((O) (n꜀)) ≠ 0) (u : E) (hu : u ≠ 0) :
    LinearIndependent E ![rulingFormRestriction W₀ (u⁻¹ • (n꜀)), rulingFormRestriction W₀ s] := by
  have hnlast := actual_gauss_root_numerator_fixed_vertex_coordinate_zero H I E e hH hd hind hGauss
    hvertex (n꜀) ⟨p, hY, h, hh, rfl⟩
  obtain ⟨bS, bN, _hLI, hbS, hbN, hsS, hnS, hsN, hnN, _hspan⟩ :=
    fixed_vertex_scaled_covectors_construct_dual_output_basis H I E hH e hd hind hGauss
      hvertex s (n꜀) hs hnlast hn
  apply ruling_form_pair_independent_of_specified_dual_values W₀ (u⁻¹ • (n꜀)) s (u • bN) bS
    ((W₀).smul_mem u hbN) hbS
  · rw [smul_dotProduct, dotProduct_smul, hnN]
    simp only [smul_eq_mul, mul_one, inv_mul_cancel₀ hu]
  · rw [dotProduct_smul, hsN, smul_zero]
  · rw [smul_dotProduct, hnS, smul_zero]
  · exact hsS

end DimensionFourDependence
