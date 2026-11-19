import DimensionFourDependence.SpecifiedGraphOutputValues

/-! # Original full output and normal values in the graph coefficient tensor -/

namespace DimensionFourDependence

open MvPolynomial Matrix
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "C₀" => closedGaussParameterField H I
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh

/-- All original outputs, retained as elements of the same actual
graph coefficient field, with their original coordinate labels. -/
noncomputable def originalGraphFullOutputCoordinate : Fin 4 → L :=
  Fin.snoc (coefficientCoordinate (K := K) (Y)) h ∘ p.symm

include hh

/-- The full coefficient-field output tuple has the exact original
source values. -/
theorem originalGraphFullOutputCoordinate_source_value (i : Fin 4) :
    (originalGraphFullOutputCoordinate H p h i : S₀) =
      algebraMap (MvPolynomial (Fin 4) K) S₀ (H i) := by
  obtain ⟨j, rfl⟩ := p.surjective i
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have hz : originalGraphFullOutputCoordinate H p h (p (Fin.last 3)) = h := by
      dsimp only [originalGraphFullOutputCoordinate, Function.comp_apply]
      rw [p.symm_apply_apply]
      exact Fin.snoc_last _ _
    exact (congrArg (fun b : L => (b : S₀)) hz).trans hh
  · simp only [originalGraphFullOutputCoordinate, Function.comp_apply, Equiv.symm_apply_apply,
      Fin.snoc_castSucc, coefficientCoordinate_coe]

/-- The two original graph parameter maps agree, using their
opaque source-value lemmas rather than unfolding field actions. -/
theorem actualClosedGaussCoefficientHom_parameter_value
    (e : RatFunc K ≃ₐ[K] C₀) (r : RatFunc K) :
    (a) (e r) = closedGaussCoefficientParameterHom H I p hY h hh e r := by
  apply Subtype.ext
  exact (original_closed_gauss_graph_inclusion_source_value H I p hY h hh (e r)).trans
    (closedGaussCoefficientParameterHom_source_value H I p hY h hh e r).symm

variable (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]

local notation "T₀" => S₀ ⊗[C₀] E
local notation "xₜ" => extendedClosedGaussSourceTensorCoordinate H I E
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E

/-- Every full original output covector has its exact coefficient
tensor value before passing to the source fraction field. -/
theorem original_graph_full_output_covector_source_tensor_value (c : Fin 4 → E) :
    aeval (xₜ) ((O) c) = coefficientTensorLinearValue (C := C₀) c
      (fun i => (originalGraphFullOutputCoordinate H p h i : S₀)) := by
  simp only [extendedClosedGaussOutputLinearPolynomial, MvPolynomial.smul_eq_C_mul,
    map_sum, map_mul, aeval_C, coefficientTensorLinearValue,
    extendedClosedGaussSourceTensorCoordinate_original_constant_polynomial_value,
    originalGraphFullOutputCoordinate_source_value H p h hh]

/-- The chosen original normal form has its exact first-invariant
source tensor value, with the same graph pivot. -/
theorem original_graph_chosen_normal_source_tensor_value
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d) (hind : ¬ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1) (e : RatFunc K ≃ₐ[K] C₀)
    (c : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h) :
    aeval (xₜ) (linearFormPolynomial (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)) =
      algebraMap E T₀ (algebraMap C₀ E (actualClosedGaussNormalCovector H I e (p 3))) *
        ((c : S₀) ⊗ₜ[C₀] (1 : E)) := by
  let ν := actualClosedGaussFirstInvariantCovector H I p hY h hh
  let pivot := algebraMap C₀ E (actualClosedGaussNormalCovector H I e (p 3))
  have hpoly : linearFormPolynomial (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0) =
      MvPolynomial.C pivot * MvPolynomial.map (algebraMap C₀ E) (linearFormPolynomial ν) := by
    simp only [linearFormPolynomial,
      extendedClosedGaussChosenRulingMatrix_first_row_eq_graph_pivot_mul H I p hY h hh E e hH hd hind hGauss,
      map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, Finset.mul_sum, pivot, ν]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hpoly, map_mul, aeval_C, extendedClosedGaussSourceTensorCoordinate_original_polynomial_value,
    actualClosedGaussFirstInvariantCovector_source_value, ← hc]
  rfl

end DimensionFourDependence
