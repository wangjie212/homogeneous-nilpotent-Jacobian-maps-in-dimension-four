import DimensionFourDependence.ConstructedAffineFiniteProjection
import DimensionFourDependence.TensorPencilHyperplaneMultiplicity

/-! # Actual finite linear projections of the original tensor pencil charts

The original ratio coordinates and actual extended pencil equation choose
the linear projection. The complete original tensor chart is finite over
the constructed two-coordinate algebra. Its transformed equation retains
the original pencil-degree bound and has full degree in the fiber.
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

/-- On every actual original tensor pencil chart, the original extended
equation and source-ratio generators construct a finite linear projection.
The actual new coordinates still generate the entire original tensor
ring, and their nonzero full-fiber-degree equation has degree at most the
original pencil degree. No finite projection or monic direction is assumed. -/
theorem actual_original_tensor_pencil_finite_linear_projection
    (e : RatFunc K ≃ₐ[K] C₀) (p q : MvPolynomial (Fin 4) K) {D : ℕ}
    (hq : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)
    (s : Fin 4 ≃ Option (Fin 3)) :
    ∃ T : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E),
      let r := finSuccEquiv' (0 : Fin 3)
      let y := fun i : Option (Fin 2) =>
        linearProjectionCoordinate T (originalTensorPencilCoordinate H I E s) (r.symm i)
      let f := renameEquiv E r
        (linearPolynomialPullback (LinearMap.toMatrix' T.toLinearMap)
          (MvPolynomial.map (algebraMap C₀ E) (closedGaussPencilChartEquation H I e p q s)))
      Algebra.adjoin E (Set.range y) = ⊤ ∧ f ≠ 0 ∧ f.degreeOf none = f.totalDegree ∧
        f.totalDegree ≤ D ∧ aeval y f = 0 ∧
        Module.Finite (affineProjectionAlgebra (k := E) y) (T₀ s) := by
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap C₀ E).injective
  obtain ⟨hf, hr, hd⟩ := original_tensor_pencil_equation_data H I E e p q hq hrel hpH hqH ht s
  obtain ⟨T, hgen, hg, hdegree, hfull, hroot, hfinite⟩ :=
    @exists_actual_affine_finite_linear_projection E (T₀ s)
      (inferInstance : Field E) (inferInstance : Infinite E)
      (inferInstance : CommRing (T₀ s)) (inferInstance : Algebra E (T₀ s)) 2
      (originalTensorPencilCoordinate H I E s) (originalTensorPencilCoordinate_adjoin H I E s)
      (MvPolynomial.map (algebraMap C₀ E) (closedGaussPencilChartEquation H I e p q s)) hf hr
  exact ⟨T, hgen, hg, hfull, hdegree.le.trans hd, hroot, hfinite⟩

end DimensionFourDependence
