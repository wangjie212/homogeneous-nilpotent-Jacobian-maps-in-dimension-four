import DimensionFourDependence.OriginalGraphTensorValues
import DimensionFourDependence.CanonicalGraphRootFactor

/-! # The same boundary field retains exact original graph output products -/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

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
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "C₀" => closedGaussParameterField H I
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh
local notation "A" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "Aₑ" => fun i => algebraMap C₀ E (e ((A) i))
local notation "y₀" => coefficientCoordinate (K := K) (Y)
local notation "n₀" => parametricRulingDenominator (closedGaussCoefficientParameterHom H I p hY h hh e) (A) (y₀)
local notation "a₀" => actualClosedGaussNormalCovector H I e (p 3)

variable {κ : Type u} [Field κ] [Algebra (coefficientField (K := K)
    (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
      (H (p i.castSucc)))) κ] [Algebra E κ]

include hd hH hh

/-- The original four-output value of every extended covector is
exactly its graph restriction paired with the original coefficient
coordinates in the same compatible boundary field. -/
theorem original_full_output_boundary_value_eq_graph_pairing
    (hσ : ∀ b : C₀, algebraMap (L) κ ((a) b) = algebraMap E κ (algebraMap C₀ E b))
    (q : Fin 4 → E) :
    (∑ i, algebraMap E κ (q i) * algebraMap (L) κ (originalGraphFullOutputCoordinate H p h i)) =
      (fun i => algebraMap E κ (graphRestrictedCovector p (Aₑ) q i)) ⬝ᵥ
        (fun i => algebraMap (L) κ ((y₀) i)) := by
  have he := specified_graph_coefficient_embedding_retains_original_euler_equation
    H I p hY h hh E hd hH e (algebraMap (L) κ) (algebraMap E κ) hσ
  rw [← Equiv.sum_comp p (fun i => algebraMap E κ (q i) *
    algebraMap (L) κ (originalGraphFullOutputCoordinate H p h i)), Fin.sum_univ_castSucc]
  have hZ (i : Fin 3) : originalGraphFullOutputCoordinate H p h (p i.castSucc) = (y₀) i := by
    simp only [originalGraphFullOutputCoordinate, Function.comp_apply, Equiv.symm_apply_apply, Fin.snoc_castSucc]
  have hZlast : originalGraphFullOutputCoordinate H p h (p 3) = h := by
    dsimp only [originalGraphFullOutputCoordinate, Function.comp_apply]
    rw [p.symm_apply_apply]
    exact Fin.snoc_last _ _
  simp only [hZ, hZlast, show (Fin.last 3 : Fin 4) = 3 from rfl, he, dotProduct,
    graphRestrictedCovector, map_add, map_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

/-- The exact canonical numerator times the original pivot-scaled
first invariant is precisely the original graph product n(Y)c.
All coefficient maps and the original graph chart are retained. -/
theorem original_canonical_boundary_numerator_normal_product_eq_graph_invariant_product
    (hσ : ∀ b : C₀, algebraMap (L) κ ((a) b) = algebraMap E κ (algebraMap C₀ E b)) (c : L) :
    (∑ i, algebraMap E κ (closedGaussCanonicalRootNumerator H I p hY h hh e E i) *
      algebraMap (L) κ (originalGraphFullOutputCoordinate H p h i)) *
        algebraMap (L) κ ((a) (a₀) * c) = algebraMap (L) κ (n₀) * algebraMap (L) κ c := by
  rw [original_full_output_boundary_value_eq_graph_pairing H I p hY h hh E hd hH e hσ]
  rw [canonical_root_numerator_graph_restriction H I p hY h hh e E]
  have hparameter (r : RatFunc K) : algebraMap E κ (algebraMap C₀ E (e r)) =
      algebraMap (L) κ (closedGaussCoefficientParameterHom H I p hY h hh e r) := by
    rw [← hσ, actualClosedGaussCoefficientHom_parameter_value H I p hY h hh e r]
  have hNvalue : (fun i : Fin 3 => algebraMap E κ ((algebraMap C₀ E (a₀))⁻¹ *
      algebraMap C₀ E (e (rationalParameterDerivative K (rationalParameterDerivative K ((A) i)))))) ⬝ᵥ
        (fun i => algebraMap (L) κ ((y₀) i)) =
      (algebraMap E κ (algebraMap C₀ E (a₀)))⁻¹ * algebraMap (L) κ (n₀) := by
    simp only [dotProduct, map_mul, map_inv₀, hparameter, parametricRulingDenominator,
      map_sum, Finset.mul_sum, mul_assoc]
  rw [hNvalue, map_mul, hσ]
  have hpivot : algebraMap E κ (algebraMap C₀ E (a₀)) ≠ 0 :=
    (map_ne_zero (algebraMap E κ)).mpr ((map_ne_zero (algebraMap C₀ E)).mpr
      (actualClosedGaussNormalCovector_graph_pivot_ne_zero H I p hY h hh e))
  field_simp [hpivot]

end DimensionFourDependence
