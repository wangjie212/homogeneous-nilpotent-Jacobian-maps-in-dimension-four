import DimensionFourDependence.TensorPencilProjectionResidue
import DimensionFourDependence.CanonicalProjectionFieldActions

/-! # The actual pencil divisor constructs its iterated rational projection field

The construction uses the original tensor chart and its original
hypersurface equation, and preserves the entire original local-ring
inclusion in its original function field.
-/

namespace DimensionFourDependence

universe u

open MvPolynomial
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" s:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (Equiv.symm s none)
local notation "T₀" s:max => S₀ s ⊗[C₀] E
local notation "Aₑ" s:max => E ⊗[C₀] closedGaussPencilChartAlgebra H I s

/-- The original tensor-pencil chart is a domain after the specified
algebraic coefficient extension. -/
theorem original_tensor_pencil_chart_isDomain
    [Algebra.IsAlgebraic C₀ E] (s : Fin 4 ≃ Option (Fin 3)) : IsDomain (T₀ s) := by
  let : IsDomain (Aₑ s) := actual_closed_gauss_extended_chart_isDomain H I s E
  let φ := originalTensorPencilCoordinateEquiv H I E s
  exact Function.Injective.isDomain φ φ.injective

/-- Every original tensor-pencil divisor constructs its actual iterated
rational projection-field action, regular polynomial-base action and
infinity-base action. All preserve the original constants and projection
coordinate values. The projection, its degree-bounded equation and the
transcendental residue parameter are constructed internally. -/
theorem actual_original_tensor_pencil_divisor_projection_field_actions
    [Algebra.IsAlgebraic C₀ E]
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] C₀)
    (hGauss : gaussImageDimension H I = 1)
    (p q : MvPolynomial (Fin 4) K) {D : ℕ}
    (hq : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)
    (s : Fin 4 ≃ Option (Fin 3))
    (Q : Ideal (normalizationRing (T₀ s))) [Q.IsPrime] (hQ : Q.height = 1) :
    let : IsDomain (T₀ s) := original_tensor_pencil_chart_isDomain H I E s
    ∃ T : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E),
      let r := finSuccEquiv' (0 : Fin 3)
      let y := fun i : Option (Fin 2) =>
        linearProjectionCoordinate T (originalTensorPencilCoordinate H I E s) (r.symm i)
      let f := renameEquiv E r
        (linearPolynomialPullback (LinearMap.toMatrix' T.toLinearMap)
          (MvPolynomial.map (algebraMap C₀ E) (closedGaussPencilChartEquation H I e p q s)))
      Algebra.adjoin E (Set.range y) = ⊤ ∧ f ≠ 0 ∧ f.degreeOf none = f.totalDegree ∧
        f.totalDegree ≤ D ∧ aeval y f = 0 ∧
        Module.Finite (affineProjectionAlgebra (k := E) y) (T₀ s) ∧
        AlgebraicIndependent E (fun j : Fin 2 => y (some j)) ∧
        canonicalProjectionFieldActions (k := E) Q (fun j => y (some j)) := by
  let A := T₀ s
  let : IsDomain A := original_tensor_pencil_chart_isDomain H I E s
  have hprojection :=
    @actual_original_tensor_pencil_divisor_projection_parameter K
      (inferInstance : Field K) (inferInstance : CharZero K) H I E
      (inferInstance : Field E) (inferInstance : Algebra C₀ E)
      (inferInstance : Algebra.IsAlgebraic C₀ E)
      d hH e hGauss p q D hq hrel hpH hqH ht s Q inferInstance hQ
  let T := hprojection.choose
  have hdata := hprojection.choose_spec
  let r := finSuccEquiv' (0 : Fin 3)
  let y : Option (Fin 2) → A := fun i =>
    linearProjectionCoordinate T (originalTensorPencilCoordinate H I E s) (r.symm i)
  have hind : AlgebraicIndependent E (fun j : Fin 2 => y (some j)) := hdata.2.2.2.2.2.2.1
  have hres : ∃ j : Fin 2, Transcendental E (IsLocalRing.residue (Localization.AtPrime Q)
      (algebraMap A (Localization.AtPrime Q) (y (some j)))) := hdata.2.2.2.2.2.2.2
  refine ⟨T, hdata.1, hdata.2.1, hdata.2.2.1, hdata.2.2.2.1,
    hdata.2.2.2.2.1, hdata.2.2.2.2.2.1, hind, ?_⟩
  exact @canonical_normalization_independent_projection_actions E A
    (inferInstance : Field E) (inferInstance : CommRing A) (inferInstance : IsDomain A)
    (inferInstance : Algebra E A) (fun j : Fin 2 => y (some j)) hind Q inferInstance hres

end DimensionFourDependence
