import DimensionFourDependence.OriginalChartCanonicalSectionOrder
import DimensionFourDependence.TensorPencilProjectionFieldActions
import DimensionFourDependence.ProjectiveAffineRatioCoordinates

/-! # Canonical normalized-frame section orders on the actual tensor pencil

The original pencil equation and its original ratio coordinates construct
all finite-projection data at every actual divisor prime. Consequently an
arbitrary section represented on the four original normalized projective
charts has local order bounded by the original pencil degree. The actual
local section value is retained throughout the construction.
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

/-- At each actual divisor of the original tensor-pencil normalization,
every nonzero section represented in all four original normalized
projective frames has order at most the original pencil degree. Its canonical local coefficient is constructed from the
original normalized frame. No local section value, finite projection,
base parameter, field action, local model or section integrality is supplied. -/
theorem actual_original_tensor_pencil_canonical_section_order_le_degree
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
    let : Field (FractionRing (T₀ s)) := inferInstance
    ∀ (x : Fin 4 → FractionRing (T₀ s))
      (sectionValue : ProjectiveNormalizedSection (k := E) x)
      (hbase : x (s.symm none) ≠ 0)
      (hratios : projectiveAffineRatioCoordinates x s =
        (fun i => algebraMap (T₀ s) (FractionRing (T₀ s)) (originalTensorPencilCoordinate H I E s i)))
      (_hsection : (sectionValue.coefficient (s.symm none) : FractionRing (T₀ s)) ≠ 0)
      (a : ℕ) (_horder : algebraMap (normalizationRing (T₀ s)) (Localization.AtPrime Q)
        (originalChartSectionNormalizationCoefficient (originalTensorPencilCoordinate H I E s)
          x sectionValue s hbase hratios) ∈
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ a), a ≤ D := by
  let A := T₀ s
  let : IsDomain A := original_tensor_pencil_chart_isDomain H I E s
  let : Field (FractionRing A) := inferInstance
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap C₀ E).injective
  let : Algebra.FiniteType C₀ (closedGaussPencilChartAlgebra H I s) :=
    closedGaussPencilChartAlgebra_finiteType H I s
  let φ := originalTensorPencilCoordinateEquiv H I E s
  let : Algebra.FiniteType E A := (inferInstance : Algebra.FiniteType E (Aₑ s)).equiv φ.symm
  dsimp only
  intro x sectionValue hbase hratios hsection a horder
  have htr : 2 ≤ Algebra.trdeg E A := (original_tensor_pencil_trdeg_two H I E hH e hGauss s).ge
  let f := MvPolynomial.map (algebraMap C₀ E) (closedGaussPencilChartEquation H I e p q s)
  have hdata := original_tensor_pencil_equation_data H I E e p q hq hrel hpH hqH ht s
  have hbound := @canonical_original_normalization_section_order_le_equation_degree E A
    (inferInstance : Field E) (inferInstance : CharZero E) (inferInstance : CommRing A)
    (inferInstance : IsDomain A) (inferInstance : Algebra E A) (inferInstance : Algebra.FiniteType E A)
    (originalTensorPencilCoordinate H I E s) (originalTensorPencilCoordinate_adjoin H I E s)
    htr f hdata.1 hdata.2.1 Q inferInstance hQ x sectionValue s hbase hratios hsection a horder
  exact hbound.trans hdata.2.2

end DimensionFourDependence
