import DimensionFourDependence.AffineSourceConeForm
import DimensionFourDependence.HomogeneousRationalRootTransfer
import DimensionFourDependence.FixedVertexRootNumerator

/-! # Both actual remaining root cases on the original affine source

The actual native root data determine the same rational root on the
original affine source after the actual algebraic coefficient extension.
Its output-linear power, nonzero denominator, nonvanishing and the two
remaining alternatives are retained. In the second alternative the full
cone formula (4.7), including its nonzero fourth coefficient, is constructed.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hd : 0 < d) (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "C₀" => closedGaussParameterField H I
local notation "T₀" => FractionRing (MvPolynomial (Fin 4) K) ⊗[C₀] E
local notation "F₀" => FractionRing T₀
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "L₀" => linearFormPolynomial ((A₀) 0)

local instance affineFixedVertexRootAlternativesDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
local instance affineFixedVertexRootAlternativesIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance affineFixedVertexRootAlternativesNativeAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual two remaining root cases on the original affine
source. The second case is the whole cone formula (4.7), with its
nonzero fourth coefficient and both ternary ruling incidences. -/
noncomputable def ActualAffineFixedVertexRootAlternatives : Prop :=
  ∃ cS cM cN : Fin 4 → E, cS ≠ 0 ∧ cM ≠ 0 ∧ cN ≠ 0 ∧ cN (Fin.last 3) = 0 ∧
    aeval (xₐ) ((O) cM) ≠ 0 ∧
    let R := aeval (xₐ) ((O) cN) * aeval (xₐ) (L₀) / aeval (xₐ) ((O) cM)
    R ≠ 0 ∧ R ^ d = aeval (xₐ) ((O) cS) ∧
      ((∃ γ : E, γ ≠ 0 ∧ R = algebraMap E F₀ γ⁻¹ * aeval (xₐ) (L₀)) ∨
        AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss R)

/-- The constructed native remaining cases give both original affine
remaining cases. The affine rational root, its exact power and denominator,
the plane formula or complete cone formula are all derived together. -/
theorem actual_chosen_root_normal_forms_construct_affine_fixed_vertex_alternatives
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (hdata : ActualChosenGaussRootNormalForms H I E hH e hd hind hGauss) :
    ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss := by
  classical
  obtain ⟨cS, cM, cN, r, hS, hM, hN, hr, hpower, hm, hformula, halt, hnumerator⟩ := hdata
  have hnlast := actual_gauss_root_numerator_fixed_vertex_coordinate_zero
    H I E e hH hd hind hGauss hvertex cN hnumerator
  have hL : aeval (w) (L₀) =
      ∑ i : Fin 4, algebraMap E (N).functionField ((A₀) 0 i) * (w) i := by
    simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X]
  have hroot : r = aeval (w) ((O) cN) * aeval (w) (L₀) / aeval (w) ((O) cM) := by
    rw [hL]
    exact hformula
  have hrel (P : MvPolynomial (Fin 4) E) (n : ℕ) (hP : P.IsHomogeneous n) :
      aeval (w) P = 0 ↔ aeval (xₐ) P = 0 :=
    (extendedClosedGauss_affine_tensor_native_homogeneous_zero_iff H I E hH e P hP).symm
  have hNh := extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH cN
  have hMh := extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH cM
  have hSh := extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH cS
  have hLh := linearFormPolynomial_homogeneous ((A₀) 0)
  have hmₐ : aeval (xₐ) ((O) cM) ≠ 0 := fun hz => hm ((hrel _ _ hMh).mpr hz)
  have hnum : aeval (w) (((O) cN) * (L₀)) ≠ 0 := by
    intro hz
    apply hr
    rw [hroot, ← map_mul, hz, zero_div]
  have hnumₐ : aeval (xₐ) ((O) cN) * aeval (xₐ) (L₀) ≠ 0 := by
    rw [← map_mul]
    exact fun hz => hnum ((hrel _ _ (hNh.mul hLh)).mpr hz)
  have hpowerₐ := homogeneous_relations_transfer_rational_root_power
    ((O) cN) ((O) cM) ((O) cS) (L₀) hNh hMh hSh hLh (w) (xₐ) hrel r hm hroot hpower
  refine ⟨cS, cM, cN, hS, hM, hN, hnlast, hmₐ, div_ne_zero hnumₐ hmₐ, hpowerₐ, ?_⟩
  rcases halt with ⟨γ, hγ, _hMN, hplane, _hplanePower⟩ | ⟨_hMN, β, _hβ, _hSN, hfactor⟩
  · left
    refine ⟨γ, hγ, ?_⟩
    apply homogeneous_relations_transfer_scaled_plane_root
      ((O) cN) ((O) cM) (L₀) hNh hMh hLh (w) (xₐ) hrel r hm hroot γ⁻¹
    rw [hL]
    exact hplane
  · right
    exact (native_characteristic_root_constructs_affine_source_fixed_vertex_cone_form
      H I E hH e hd hind hGauss hvertex cM cN r hr hm hroot hfactor).2.2

end DimensionFourDependence
