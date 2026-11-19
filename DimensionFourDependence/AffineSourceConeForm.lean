import DimensionFourDependence.NativeFixedVertexConeForm
import DimensionFourDependence.HomogeneousConeFormulaTransfer
import DimensionFourDependence.ModifiedCubicFiberBoundary

/-! # The actual affine source retains the constructed full cone formula

The original source tensor embeds in its fraction field. Its exact
homogeneous relations agree with the actual native normalized pencil.
The complete rational cone formula therefore returns to the original
four affine source coordinates, with the same algebraic coefficients.
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

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "F₀" => FractionRing T₀

local instance affineSourceConeFormDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain

/-- The actual four original affine source coordinates in the
fraction field of their original algebraic coefficient extension. -/
noncomputable def extendedClosedGaussAffineTensorCoordinate (i : Fin 4) : F₀ :=
  algebraMap T₀ F₀ (extendedClosedGaussSourceTensorCoordinate H I E i)

variable {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E

local instance affineSourceConeFormIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance affineSourceConeFormNativeAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The full original affine source and native projective pencil
have exactly the same homogeneous vanishing identities after the actual
algebraic extension of closed Gauss coefficients. -/
theorem extendedClosedGauss_affine_tensor_native_homogeneous_zero_iff
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n) :
    aeval (xₐ) P = 0 ↔ aeval (w) P = 0 := by
  have he := comp_aeval_apply (extendedClosedGaussSourceTensorCoordinate H I E)
    (IsScalarTower.toAlgHom E T₀ F₀) P
  change algebraMap T₀ F₀ (aeval (extendedClosedGaussSourceTensorCoordinate H I E) P) = aeval (xₐ) P at he
  rw [← he]
  exact (map_eq_zero_iff _ (IsFractionRing.injective T₀ F₀)).trans
    (extendedClosedGauss_source_tensor_native_homogeneous_zero_iff H I E hH e P hP)

variable (hd : 0 < d) (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "L₀" => linearFormPolynomial ((A₀) 0)
local notation "Yₐ" => fun i => aeval (xₐ) (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i))

/-- The whole fixed-vertex cone formula on the original affine
source after the actual algebraic parameter-coefficient extension. -/
noncomputable def AffineSourceFixedVertexConeRootForm (r : F₀) : Prop :=
  ∃ (V : Fin 3 → E) (a b : E), V ≠ 0 ∧ b ≠ 0 ∧
    (∀ q : Fin 2, (∑ i : Fin 3, (A₀) q i.castSucc * V i) = 0) ∧
    (∀ i : Fin 3, (Yₐ) i.castSucc = algebraMap E F₀ (V i) * r ^ d) ∧
    (Yₐ) (Fin.last 3) = algebraMap E F₀ a * r ^ d + algebraMap E F₀ b * r ^ (d - 1) *
      (∑ i : Fin 3, algebraMap E F₀ ((A₀) 0 i.castSucc) * (xₐ) i.castSucc)

/-- The actual characteristic root factorization constructs the
complete original affine cone formula (4.7), with its nonzero last
coefficient and exact rational root denominator retained. -/
theorem native_characteristic_root_constructs_affine_source_fixed_vertex_cone_form
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (cM cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hm : aeval (w) ((O) cM) ≠ 0)
    (hroot : r = aeval (w) ((O) cN) * aeval (w) (L₀) / aeval (w) ((O) cM))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e hd hind hGauss cN r) :
    aeval (xₐ) ((O) cM) ≠ 0 ∧
      let R := aeval (xₐ) ((O) cN) * aeval (xₐ) (L₀) / aeval (xₐ) ((O) cM)
      R ≠ 0 ∧ AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss R := by
  classical
  obtain ⟨V, a, b, hV, hb, hinc, hfirst, hlast⟩ :=
    native_characteristic_root_constructs_full_fixed_vertex_cone_form H I E hH e hd hind hGauss hvertex cN r hfactor
  have hcol := extended_chosen_ruling_fixed_vertex_last_column H I E hH hd hind hGauss hvertex
  have hL (F : Type u) [Field F] [Algebra E F] (x : Fin 4 → F) :
      aeval x (L₀) = ∑ i : Fin 3, algebraMap E F ((A₀) 0 i.castSucc) * x i.castSucc := by
    simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X]
    rw [Fin.sum_univ_castSucc, hcol, map_zero, zero_mul, add_zero]
  have hlast' : aeval (w) (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H (Fin.last 3))) =
      algebraMap E (N).functionField a * r ^ d + algebraMap E (N).functionField b * r ^ (d - 1) *
        aeval (w) (L₀) := by rw [hL]; exact hlast
  obtain ⟨hmₐ, hrₐ, hfirstₐ, hlastₐ⟩ := homogeneous_relations_transfer_full_rational_cone_form
    (fun i => MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i)) hd
    (fun i => (hH i).map _) ((O) cN) ((O) cM) (L₀)
    (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH cN)
    (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH cM)
    (linearFormPolynomial_homogeneous _) (w) (xₐ)
    (fun P _ hP => (extendedClosedGauss_affine_tensor_native_homogeneous_zero_iff H I E hH e P hP).symm)
    r hr hm hroot V a b hfirst hlast'
  refine ⟨hmₐ, hrₐ, V, a, b, hV, hb, hinc, hfirstₐ, ?_⟩
  simpa only [hL] using hlastₐ

end DimensionFourDependence
