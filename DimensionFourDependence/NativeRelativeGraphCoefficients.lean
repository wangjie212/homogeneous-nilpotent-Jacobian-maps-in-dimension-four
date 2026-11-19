import DimensionFourDependence.RelativeSourceCoefficientRealization
import DimensionFourDependence.NativeScaledFullOutputEmbedding
import DimensionFourDependence.SameComponentGraphCoefficients

/-! # The actual native relative constants retain all original graph coefficients -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E
local notation "D₀" => polynomialOutputField H
local notation "L" => coefficientField (K := K)
  (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc)))
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "Cᵣ" => RatFunc (RatFunc E)
local notation "Gᵣ" => RatFunc (N).functionField

local instance nativeRelativeGraphCoefficientsDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
local instance nativeRelativeGraphCoefficientsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeRelativeGraphCoefficientsExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

noncomputable local instance nativeRelativeGraphCoefficientsOriginalAlgebra : Algebra K (N).functionField :=
  extendedClosedGaussOriginalSourceAlgebra H I E hH e

local notation "Jᵣ" => algebraicClosure Cᵣ Gᵣ

include hrank

/-- The actual independently scaled source realizes every original
fiber coefficient inside its relative constants over E(lambda)(s).
The same embedding retains all original closed Gauss coefficients
and the entire original full output field, and makes those relative
constants algebraic over the original fiber coefficient field. -/
theorem native_scaled_source_constructs_same_relative_graph_coefficients
    (P : MvPolynomial (Fin 4) E) (hP : aeval (R := E) (w) P ≠ 0)
    (α : RatFunc E →ₐ[E] (N).functionField) :
    letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
    ∀ (γ : Cᵣ →ₐ[RatFunc E] Gᵣ) (ε : D₀ →+* Cᵣ),
      (∀ c : K, ε (algebraMap K D₀ c) = RatFunc.C (RatFunc.C ((ι) c))) →
      (∀ q : D₀, γ (ε q) = nativeIndependentScaleSourceFieldHom H I E hH e P hP (q : S₀)) →
      (letI : Algebra D₀ Cᵣ := ε.toAlgebra; Algebra.IsAlgebraic D₀ Cᵣ) →
      letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra
      ∃ g : (L) →+* Jᵣ,
        (∀ l : L, algebraMap Jᵣ Gᵣ (g l) = nativeIndependentScaleSourceFieldHom H I E hH e P hP (l : S₀)) ∧
        (∀ c : K, g (algebraMap K (L) c) = algebraMap Cᵣ Jᵣ (RatFunc.C (RatFunc.C ((ι) c)))) ∧
        (∀ c : C₀, g ((a) c) = algebraMap Cᵣ Jᵣ (RatFunc.C (RatFunc.C (algebraMap C₀ E c)))) ∧
        (∀ (q : D₀) (l : L), (l : S₀) = (q : S₀) → g l = algebraMap Cᵣ Jᵣ (ε q)) ∧
        letI : Algebra (L) Jᵣ := g.toAlgebra
        Algebra.IsAlgebraic (L) Jᵣ := by
  letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
  intro γ ε hεK hcompat halg
  letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra
  letI : Algebra D₀ Cᵣ := ε.toAlgebra
  letI : Algebra.IsAlgebraic D₀ Cᵣ := halg
  letI : Algebra D₀ Gᵣ := (γ.toRingHom.comp ε).toAlgebra
  letI : IsScalarTower D₀ Cᵣ Gᵣ := IsScalarTower.of_algebraMap_eq' rfl
  have hr : (rationalJacobian (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))).rank = 3 := by
    rw [rationalJacobian_polynomial]
    exact hrank
  letI : Algebra D₀ (L) := fullOutputCoefficientAlgebra _ hr p hY
  letI : IsScalarTower D₀ (L) S₀ := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsAlgebraic D₀ (L) := fullOutputCoefficient_isAlgebraic _ hr p hY
  let Φ := nativeIndependentScaleSourceFieldHom H I E hH e P hP
  let ΦD : S₀ →ₐ[D₀] Gᵣ := { Φ.toRingHom with commutes' := fun q => (hcompat q).symm }
  have hAlg (l : L) : IsAlgebraic Cᵣ (Φ (l : S₀)) :=
    algebraic_source_coefficient_images_algebraic_over_extended_constants ΦD l
  let g : (L) →+* Jᵣ := sourceCoefficientRelativeClosureHom Φ.toRingHom hAlg
  have hg (l : L) : algebraMap Jᵣ Gᵣ (g l) = Φ (l : S₀) := rfl
  have hgD (q : D₀) (l : L) (hl : (l : S₀) = (q : S₀)) : g l = algebraMap Cᵣ Jᵣ (ε q) := by
    apply Subtype.ext
    change Φ (l : S₀) = γ (ε q)
    rw [hl]
    exact (hcompat q).symm
  have hγC (b : RatFunc E) : γ (RatFunc.C b) = RatFunc.C (α b) :=
    (γ.commutes b).trans (IsScalarTower.algebraMap_apply (RatFunc E) (N).functionField Gᵣ b)
  have hαC (b : E) : α (RatFunc.C b) = algebraMap E (N).functionField b := α.commutes b
  refine ⟨g, hg, ?_, ?_, hgD, ?_⟩
  · intro c
    apply Subtype.ext
    change Φ (algebraMap (L) S₀ (algebraMap K (L) c)) = γ (RatFunc.C (RatFunc.C ((ι) c)))
    rw [← IsScalarTower.algebraMap_apply K (L) S₀,
      nativeIndependentScaleSourceFieldHom_coefficient, hγC, hαC]
  · intro c
    apply Subtype.ext
    change Φ (algebraMap (L) S₀ ((a) c)) = γ (RatFunc.C (RatFunc.C (algebraMap C₀ E c)))
    rw [original_closed_gauss_graph_inclusion_source_value H I p hY h hh,
      nativeIndependentScaleSourceFieldHom_closed_coefficient, hγC, hαC]
  · exact relative_constant_field_isAlgebraic_over_compatible_source_coefficients
      (D := D₀) g (fun q => hgD q (algebraMap D₀ (L) q) rfl)

end DimensionFourDependence
