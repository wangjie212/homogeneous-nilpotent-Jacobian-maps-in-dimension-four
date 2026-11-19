import DimensionFourDependence.TensorPencilFiniteProjection
import DimensionFourDependence.CanonicalProjectionResidueParameter

/-! # Actual pencil divisors supply independent finite-projection base parameters

The original tensor atlas, original degree-bounded equation and intrinsic
surface dimension construct a finite projection with independent base
coordinates. At every actual height-one normalization prime, one of those
same base coordinates has transcendental residue. No independent
projection coordinates, auxiliary local model or residue parameter are
assumed.
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

/-- Every actual divisor prime of the original tensor-chart
normalization supplies a constructed finite linear projection whose two
base coordinates are independent and one of whose base residues is
transcendental. Its actual equation retains the original degree bound and
full fiber degree, and its coordinates generate the entire original chart. -/
theorem actual_original_tensor_pencil_divisor_projection_parameter
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
        ∃ j : Fin 2, Transcendental E (IsLocalRing.residue (Localization.AtPrime Q)
          (algebraMap (T₀ s) (Localization.AtPrime Q) (y (some j)))) := by
  let A := T₀ s
  let φ := originalTensorPencilCoordinateEquiv H I E s
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap C₀ E).injective
  let : Algebra.FiniteType C₀ (closedGaussPencilChartAlgebra H I s) :=
    closedGaussPencilChartAlgebra_finiteType H I s
  let : IsDomain (Aₑ s) := actual_closed_gauss_extended_chart_isDomain H I s E
  let : IsDomain A := Function.Injective.isDomain φ φ.injective
  let : Algebra.FiniteType E A := (inferInstance : Algebra.FiniteType E (Aₑ s)).equiv φ.symm
  have htr : 2 ≤ Algebra.trdeg E A :=
    (original_tensor_pencil_trdeg_two H I E hH e hGauss s).ge
  have hprojection :=
    @actual_original_tensor_pencil_finite_linear_projection K
      (inferInstance : Field K) (inferInstance : CharZero K) H I E
      (inferInstance : Field E) (inferInstance : Algebra C₀ E)
      e p q D hq hrel hpH hqH ht s
  let T := hprojection.choose
  have hdata := hprojection.choose_spec
  let r := finSuccEquiv' (0 : Fin 3)
  let y : Option (Fin 2) → A := fun i =>
    linearProjectionCoordinate T (originalTensorPencilCoordinate H I E s) (r.symm i)
  have hfinite : Module.Finite (affineProjectionAlgebra (k := E) y) A := hdata.2.2.2.2.2
  refine ⟨T, hdata.1, hdata.2.1, hdata.2.2.1, hdata.2.2.2.1, hdata.2.2.2.2.1, hfinite, ?_, ?_⟩
  · exact @affine_finite_surface_projection_algebraicIndependent E A
      (inferInstance : Field E) (inferInstance : CommRing A) (inferInstance : IsDomain A)
      (inferInstance : Algebra E A) y htr hfinite
  · exact @canonical_normalization_finite_projection_transcendental_residue E A
      (inferInstance : Field E) (inferInstance : CharZero E) (inferInstance : CommRing A)
      (inferInstance : IsDomain A) (inferInstance : Algebra E A)
      (inferInstance : Algebra.FiniteType E A) y hfinite htr Q inferInstance hQ

end DimensionFourDependence
