import DimensionFourDependence.ThreeAffineHyperplaneMultiplicity
import DimensionFourDependence.ExtendedPencilCoordinateMultiplicity
import DimensionFourDependence.ProjectiveChartFunctionField

/-! # Every hyperplane on an original tensor normalization chart has bounded order

These are the original ratio rings in the tensor order used by the
actual global normalization atlas. A coefficient-linear comparison
preserves each original coordinate value and the actual pencil equation.
Every nonzero affine linear section then has order at most the pencil
degree at every height-one prime of the canonical normalization.
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

variable {K : Type u} [Field K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" s:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (Equiv.symm s none)
local notation "T₀" s:max => S₀ s ⊗[C₀] E
local notation "Aₑ" s:max => E ⊗[C₀] closedGaussPencilChartAlgebra H I s

/-- The original three source ratios in the global atlas's tensor order. -/
noncomputable def originalTensorPencilCoordinate
    (s : Fin 4 ≃ Option (Fin 3)) (i : Fin 3) : T₀ s :=
  projectiveChartTransition (C := C₀) (rationalCoordinate (K := K) (n := 4))
    (s.symm none) (s.symm (some i)) ⊗ₜ[C₀] (1 : E)

/-- The atlas tensor chart and the three-coordinate tensor chart agree
over the entire extended coefficient field. -/
noncomputable def originalTensorPencilCoordinateEquiv
    (s : Fin 4 ≃ Option (Fin 3)) : T₀ s ≃ₐ[E] Aₑ s := by
  let b : S₀ s ≃ₐ[C₀] closedGaussPencilChartAlgebra H I s :=
    (Subalgebra.equivOfEq _ _ (closedGaussPencilChartAlgebra_eq_projectiveCoordinateChart H I s)).symm
  let t : E ⊗[C₀] S₀ s ≃ₐ[E] Aₑ s :=
    { (Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[C₀] E) b).toRingEquiv with
      commutes' := fun c => by simp }
  exact (Algebra.TensorProduct.commRight C₀ E (S₀ s)).symm.trans t

/-- The comparison retains each original source-ratio coordinate. -/
theorem originalTensorPencilCoordinateEquiv_coordinate
    (s : Fin 4 ≃ Option (Fin 3)) (i : Fin 3) :
    originalTensorPencilCoordinateEquiv H I E s (originalTensorPencilCoordinate H I E s i) =
      extendedGaussPencilChartCoordinate H I E s i := by
  change (1 : E) ⊗ₜ[C₀]
      ((Subalgebra.equivOfEq _ _ (closedGaussPencilChartAlgebra_eq_projectiveCoordinateChart H I s)).symm
        (projectiveChartTransition (C := C₀) (rationalCoordinate (K := K) (n := 4))
          (s.symm none) (s.symm (some i)))) = _
  congr 1

/-- Original ratio coordinates generate the actual atlas tensor chart. -/
theorem originalTensorPencilCoordinate_adjoin
    (s : Fin 4 ≃ Option (Fin 3)) :
    Algebra.adjoin E (Set.range (originalTensorPencilCoordinate H I E s)) = ⊤ := by
  let φ := originalTensorPencilCoordinateEquiv H I E s
  apply Subalgebra.map_injective (f := φ.toAlgHom) φ.injective
  rw [AlgHom.map_adjoin, Algebra.map_top, (AlgHom.range_eq_top φ.toAlgHom).mpr φ.surjective, ← Set.range_comp]
  have hcoords : φ.toAlgHom ∘ originalTensorPencilCoordinate H I E s =
      extendedGaussPencilChartCoordinate H I E s :=
    funext (originalTensorPencilCoordinateEquiv_coordinate H I E s)
  rw [hcoords]
  exact extendedGaussPencilChartCoordinate_adjoin H I E s

/-- The original atlas tensor coordinates satisfy the original extended
pencil equation with the unchanged degree bound. -/
theorem original_tensor_pencil_equation_data
    (e : RatFunc K ≃ₐ[K] C₀) (p q : MvPolynomial (Fin 4) K) {D : ℕ}
    (hq : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)
    (s : Fin 4 ≃ Option (Fin 3)) :
    MvPolynomial.map (algebraMap C₀ E) (closedGaussPencilChartEquation H I e p q s) ≠ 0 ∧
      aeval (originalTensorPencilCoordinate H I E s)
        (MvPolynomial.map (algebraMap C₀ E) (closedGaussPencilChartEquation H I e p q s)) = 0 ∧
      (MvPolynomial.map (algebraMap C₀ E)
        (closedGaussPencilChartEquation H I e p q s)).totalDegree ≤ D := by
  obtain ⟨hf, hr, hd⟩ := actual_extended_gauss_pencil_chart_equation_data H I E e p q hq hrel hpH hqH ht s
  refine ⟨hf, ?_, hd⟩
  let φ := originalTensorPencilCoordinateEquiv H I E s
  apply φ.injective
  change φ.toAlgHom (aeval (originalTensorPencilCoordinate H I E s)
    (MvPolynomial.map (algebraMap C₀ E) (closedGaussPencilChartEquation H I e p q s))) = φ.toAlgHom 0
  rw [map_zero, comp_aeval_apply]
  have hcoords : (fun i => φ.toAlgHom (originalTensorPencilCoordinate H I E s i)) =
      extendedGaussPencilChartCoordinate H I E s :=
    funext (originalTensorPencilCoordinateEquiv_coordinate H I E s)
  rwa [hcoords]

variable [CharZero K]

/-- The actual atlas tensor chart has relative transcendence degree two. -/
theorem original_tensor_pencil_trdeg_two
    [Algebra.IsAlgebraic C₀ E]
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] C₀)
    (hGauss : gaussImageDimension H I = 1) (s : Fin 4 ≃ Option (Fin 3)) :
    Algebra.trdeg E (T₀ s) = 2 :=
  (originalTensorPencilCoordinateEquiv H I E s).trdeg_eq.trans
    (actual_extended_gauss_pencil_chart_trdeg_two H I E hH e hGauss s)

/-- At every height-one prime of an original tensor normalization chart,
each nonzero hyperplane section over the extended field has order at
most the original pencil degree. No chosen pivot, projection or field
generator is supplied as an assumption. -/
theorem actual_original_tensor_pencil_hyperplane_order_le_degree
    [Algebra.IsAlgebraic C₀ E]
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] C₀)
    (hGauss : gaussImageDimension H I = 1)
    (p q : MvPolynomial (Fin 4) K) {D : ℕ}
    (hq : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)
    (s : Fin 4 ≃ Option (Fin 3)) (b : E) (c : Fin 3 → E)
    (Q : Ideal (normalizationRing (T₀ s))) [Q.IsPrime] (hQ : Q.height = 1)
    (hz0 : algebraMap E (T₀ s) b + ∑ i, algebraMap E (T₀ s) (c i) * originalTensorPencilCoordinate H I E s i ≠ 0)
    (hz : algebraMap (T₀ s) (normalizationRing (T₀ s))
      (algebraMap E (T₀ s) b + ∑ i, algebraMap E (T₀ s) (c i) * originalTensorPencilCoordinate H I E s i) ∈ Q)
    (a : ℕ) (horder : algebraMap (T₀ s) (Localization.AtPrime Q)
      (algebraMap E (T₀ s) b + ∑ i, algebraMap E (T₀ s) (c i) * originalTensorPencilCoordinate H I E s i) ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ a) : a ≤ D := by
  let T := T₀ s
  let φ := originalTensorPencilCoordinateEquiv H I E s
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap C₀ E).injective
  let : Algebra.FiniteType C₀ (closedGaussPencilChartAlgebra H I s) := closedGaussPencilChartAlgebra_finiteType H I s
  let : IsDomain (Aₑ s) := actual_closed_gauss_extended_chart_isDomain H I s E
  let : IsDomain T := Function.Injective.isDomain φ φ.injective
  let : Algebra.FiniteType E T := (inferInstance : Algebra.FiniteType E (Aₑ s)).equiv φ.symm
  have htr : 2 ≤ Algebra.trdeg E T := by rw [original_tensor_pencil_trdeg_two H I E hH e hGauss s]
  obtain ⟨hf, hr, hd⟩ := original_tensor_pencil_equation_data H I E e p q hq hrel hpH hqH ht s
  have h := canonical_normalization_affine_linear_order_le_totalDegree
    (originalTensorPencilCoordinate H I E s) (originalTensorPencilCoordinate_adjoin H I E s)
    htr b c _ hf hr Q hQ hz0 hz a horder
  exact h.trans hd

end DimensionFourDependence
