import DimensionFourDependence.TernaryGraphPlaneInvariant
import DimensionFourDependence.PlanarNilpotentDependence

/-! # Restricting original constant covectors to the graph direction plane -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u v
set_option maxHeartbeats 2000000

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- Pull an original constant covector back along the linear part of
the affine graph of the generic ternary curve. -/
noncomputable def ternaryGraphRestrictedCovector (p q : L) (l : Fin 3 → K) : Fin 2 → L :=
  ![algebraMap K L (l 0) + algebraMap K L (l 2) * p,
    algebraMap K L (l 1) + algebraMap K L (l 2) * q]

theorem ternaryGraphRestrictedCovector_direction_value
    {A : Type v} [Field A] [Algebra K A] [Algebra L A] [IsScalarTower K L A]
    (p q : L) (l : Fin 3 → K) (e : Fin 2 → A) :
    aeval (![e 0, e 1, algebraMap L A p * e 0 + algebraMap L A q * e 1] : Fin 3 → A)
        (linearFormPolynomial l) =
      algebraMap L A (ternaryGraphRestrictedCovector p q l 0) * e 0 +
        algebraMap L A (ternaryGraphRestrictedCovector p q l 1) * e 1 := by
  simp only [linearFormPolynomial, Fin.sum_univ_three]
  simp only [map_add, map_mul, aeval_C, aeval_X]
  change algebraMap K A (l 0) * e 0 + algebraMap K A (l 1) * e 1 +
      algebraMap K A (l 2) * (algebraMap L A p * e 0 + algebraMap L A q * e 1) =
    algebraMap L A (algebraMap K L (l 0) + algebraMap K L (l 2) * p) * e 0 +
      algebraMap L A (algebraMap K L (l 1) + algebraMap K L (l 2) * q) * e 1
  simp only [map_add, map_mul, ← IsScalarTower.algebraMap_apply K L A]
  ring

variable [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)
local notation "∂" => (rationalPartial (K := K) (n := 3))

/-- A nonzero original covector cannot annihilate the whole graph
direction plane. The graph chain rule would force a constant relation
among the normalized polynomial outputs. -/
theorem normalized_independent_ternary_graph_restricted_covector_ne_zero
    (H : Fin 3 → R₃) (h0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (H i) = 0)
    (hind : ¬ComponentsDependent H)
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y)
    (hpair : ∀ i : Fin 2, Y i = ι (H i.castSucc))
    (w : coefficientField (K := K) Y) (hw : (w : F) = ι (H 2))
    (l : Fin 3 → K) (hl : l ≠ 0) :
    ternaryGraphRestrictedCovector (coefficientPartial Y hY 0 w)
      (coefficientPartial Y hY 1 w) l ≠ 0 := by
  intro hz
  let E := coefficientField (K := K) Y
  let : IsScalarTower K E F := coefficientFieldScalarTower Y
  let p := coefficientPartial Y hY 0 w
  let q := coefficientPartial Y hY 1 w
  have hR (i : Fin 2) : (algebraMap E F) (ternaryGraphRestrictedCovector p q l i) = 0 := by
    rw [congrFun hz i, Pi.zero_apply, map_zero]
  have hl₀ : algebraMap K F (l 0) + algebraMap K F (l 2) * (p : F) = 0 := by
    have h := hR 0
    change algebraMap E F (algebraMap K E (l 0) + algebraMap K E (l 2) * p) = 0 at h
    simpa only [map_add, map_mul, ← IsScalarTower.algebraMap_apply K E F,
      IntermediateField.algebraMap_apply] using h
  have hl₁ : algebraMap K F (l 1) + algebraMap K F (l 2) * (q : F) = 0 := by
    have h := hR 1
    change algebraMap E F (algebraMap K E (l 1) + algebraMap K E (l 2) * q) = 0 at h
    simpa only [map_add, map_mul, ← IsScalarTower.algebraMap_apply K E F,
      IntermediateField.algebraMap_apply] using h
  let U := ∑ i, C (l i) * H i
  have hU0 : aeval (fun _ : Fin 3 => (0 : K)) U = 0 := by
    change aeval (fun _ : Fin 3 => (0 : K)) (∑ i, C (l i) * H i) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_mul, h0 i, mul_zero]
  have hpart (j : Fin 3) : pderiv j U = 0 := by
    have hG : ∂ j (ι (H 2)) = (p : F) * ∂ j (ι (H 0)) + (q : F) * ∂ j (ι (H 1)) := by
      rw [← hw, coefficient_chain_rule Y hY, Fin.sum_univ_two, hpair, hpair]
      change ∂ j (ι (H 0)) * (p : F) + ∂ j (ι (H 1)) * (q : F) = _
      ring
    apply IsFractionRing.injective R₃ F
    change ι (pderiv j (∑ i, C (l i) * H i)) = ι 0
    rw [Fin.sum_univ_three]
    simp only [map_add, pderiv_C_mul, map_mul, map_zero]
    simp only [← algebraMap_eq, ← IsScalarTower.algebraMap_apply K R₃ F, ← rationalPartial_polynomial]
    change algebraMap K F (l 0) * ∂ j (ι (H 0)) +
      algebraMap K F (l 1) * ∂ j (ι (H 1)) + algebraMap K F (l 2) * ∂ j (ι (H 2)) = 0
    rw [hG]
    linear_combination (∂ j (ι (H 0))) * hl₀ + (∂ j (ι (H 1))) * hl₁
  have hU := normalized_polynomial_eq_zero_of_partials_zero U hU0 hpart
  exact hind ⟨l, hl, by simpa [U, smul_eq_C_mul] using hU⟩

end DimensionFourDependence
