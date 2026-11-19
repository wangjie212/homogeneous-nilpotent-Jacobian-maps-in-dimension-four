import DimensionFourDependence.ExtendedChosenGaussRuling
import DimensionFourDependence.NativePencilSourceDivisorExclusion

/-! # Independent actual ruling forms supply the full conditional branch exclusion after (4.4) -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

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
  [Module.Finite (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (hd : 0 < d) (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "P₀" => AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)
local notation "W₀" => LinearMap.ker
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin'

local instance nativeIndependentRulingExclusionIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeIndependentRulingExclusionAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- In the paper's independent m,n case, the actual relation
s=alpha m+beta n with alpha nonzero supplies the component span and
the binary output relation. Under the original rational root formula
and the actual dense spread-out source-divisor image hypothesis, the
configuration is impossible. No component-span equations, ruling dimension,
pencil presentation, common factor or numerical degree bounds are inputs. -/
theorem no_actual_independent_ruling_rational_root_spread_source_divisor
    (ν cS cM cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS))
    (α β : E) (hα : α ≠ 0)
    (hMN : LinearIndependent E ![rulingFormRestriction W₀ cM, rulingFormRestriction W₀ cN])
    (hlinear : rulingFormRestriction W₀ cS = α • rulingFormRestriction W₀ cM +
      β • rulingFormRestriction W₀ cN)
    (hm : aeval w (extendedClosedGaussOutputLinearPolynomial H I E cM) ≠ 0)
    (hformula : r = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) *
      (∑ i, algebraMap E (N).functionField (ν i) * w i) /
        aeval w (extendedClosedGaussOutputLinearPolynomial H I E cM))
    (model : ClosedGaussParameterSchemeModel H I E)
    (Z : Set N) (hZ : IsIrreducible Z) (hZclosed : IsClosed Z)
    (D₀ : Set P₀) (hD : IsIrreducible D₀) (hDclosed : IsClosed D₀)
    (hdiv : Order.coheight hD.genericPoint = 1)
    (himage : closure (Set.range
      (nativeClosedGaussPencilSpreadFamilySourceMorphism H I E hH e model Z hZ)) = D₀)
    (a : Fin 4) (ha : hZ.genericPoint ∈ V a)
    (hvan : (N).presheaf.germ (V a) hZ.genericPoint ha
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
          (extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β) a) ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk hZ.genericPoint)) : False := by
  have hSN := independent_ruling_forms_of_nonzero_binary_coefficient
    (rulingFormRestriction W₀ cS) (rulingFormRestriction W₀ cM)
    (rulingFormRestriction W₀ cN) α β hα hMN hlinear
  obtain ⟨bS, bN, hspan⟩ := extendedClosedGauss_native_output_span_of_chosen_ruling_forms
    H I E hH e hd hind hGauss cS cN hSN
  have hvalue := extendedClosedGauss_chosen_ruling_binary_output_relation
    H I E hH e hd hind hGauss cS cM cN α β hlinear
  obtain ⟨p, q, D, _hD, _hp, hq, hpH, hqH, hrel, ht⟩ :=
    actual_closed_gauss_parameter_reduced_homogeneous_source_quotient H hH I e
  obtain ⟨g, P, c, _hc, hg, hgh, hP, hprim, hHP, _hPdeg⟩ :=
    exists_primitive_factorization_common_degree_le_sub_two H hH hind I
  exact no_actual_native_pencil_rational_root_spread_source_divisor H I E hH e hGauss
    p q hq hrel hpH hqH ht hind ν cS cM cN r hr hd hroot α β hvalue hm hformula
    bS bN hspan model Z hZ hZclosed D₀ hD hDclosed hdiv himage a ha hvan
    P g hg hgh hP hprim hHP

end DimensionFourDependence
