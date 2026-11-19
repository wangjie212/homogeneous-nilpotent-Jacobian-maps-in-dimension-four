import DimensionFourDependence.SegreZeroPairingFiberEquations
import DimensionFourDependence.SegreNonzeroPairingExclusion

/-! # The actual zero first invariant identifies the original source determinant and nonzero second invariant -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] coefficientFieldScalarTower

set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual zero first invariant and original second-invariant
definition construct rq=-Delta(X) in the original source fraction field.
The original second invariant is consequently nonzero. -/
theorem original_segre_zero_first_invariant_second_radial_product_and_nonzero
    (H : Fin 4 → R₀) (hind : ¬ComponentsDependent H)
    (hY : AlgebraicIndependent K (segreOriginalOutputTriple H))
    (q : coefficientField (K := K) (segreOriginalOutputTriple H))
    (hc : firstFiberInvariantInChart (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY
      (segreOriginalCoefficientGraph H) = 0)
    (hq : (q : S₀) = secondFiberInvariant (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY
      (segreOriginalCoefficientGraph H) 0) :
    algebraMap R₀ S₀ (H 0) * (q : S₀) = -algebraMap R₀ S₀ (standardRulingPolynomial (F := K)) ∧ q ≠ 0 := by
  let L := coefficientField (K := K) (segreOriginalOutputTriple H)
  let U : Fin 3 → L := coefficientCoordinate (K := K) (segreOriginalOutputTriple H)
  let δ : Fin 3 → Derivation K L L := coefficientPartial (segreOriginalOutputTriple H) hY
  let x : Fin 4 → S₀ := rationalCoordinate (K := K)
  have hcast0 : (0 : Fin 3).castSucc = (0 : Fin 4) := by decide
  have hcast1 : (1 : Fin 3).castSucc = (1 : Fin 4) := by decide
  have hcast2 : (2 : Fin 3).castSucc = (2 : Fin 4) := by decide
  have hU0 : U 0 ≠ 0 := by
    intro h
    exact original_segre_first_output_ne_zero H hind
      (congrArg (fun a : L => (a : S₀)) h)
  have hcoord (i j : Fin 3) : δ i (U j) = if j = i then 1 else 0 :=
    coefficientPartial_coordinate (segreOriginalOutputTriple H) hY i j
  have hgraphSum : x 3 = ∑ i : Fin 3, algebraMap L S₀ (δ i (segreGraphFunction U)) * x i.castSucc := by
    exact sub_eq_zero.mp hc
  have hgraph : x 3 = algebraMap L S₀ (-U 1 * U 2 / U 0 ^ 2) * x 0 +
      algebraMap L S₀ (U 2 / U 0) * x 1 + algebraMap L S₀ (U 1 / U 0) * x 2 := by
    rw [hgraphSum]
    simp only [segre_graph_gradient δ U hcoord hU0, Fin.sum_univ_succ,
      Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]
    change algebraMap L S₀ (-U 1 * U 2 / U 0 ^ 2) * x 0 +
      (algebraMap L S₀ (U 2 / U 0) * x 1 + algebraMap L S₀ (U 1 / U 0) * x 2) = _
    ring
  have hqExpression : algebraMap L S₀ q =
      quadraticExpression 0 ((derivationHessian δ (segreGraphFunction U)).map (algebraMap L S₀))
        (fun i : Fin 3 => x i.castSucc) := by
    change (q : S₀) = _
    rw [hq]
    unfold secondFiberInvariant
    congr 1
    · funext i
      simp
  have hquad : algebraMap L S₀ q =
      (x 1 - algebraMap L S₀ (U 1) / algebraMap L S₀ (U 0) * x 0) *
        (x 2 - algebraMap L S₀ (U 2) / algebraMap L S₀ (U 0) * x 0) / algebraMap L S₀ (U 0) := by
    rw [hqExpression, segre_zero_gradient_quadratic_expression δ U hcoord hU0]
    simp only [hcast0, hcast1, hcast2]
  have he := segre_zero_pairing_second_invariant_radial_product_is_negative_determinant U hU0 x q hgraph hquad
  have hprod : algebraMap R₀ S₀ (H 0) * (q : S₀) =
      -algebraMap R₀ S₀ (standardRulingPolynomial (F := K)) := by
    have hu : algebraMap L S₀ (U 0) = algebraMap R₀ S₀ (H 0) := rfl
    have hqmap : algebraMap L S₀ q = (q : S₀) := rfl
    rw [map_mul, hu, hqmap] at he
    simpa only [standardRulingPolynomial, map_sub, map_mul, x, rationalCoordinate] using he
  refine ⟨hprod, ?_⟩
  intro hq0
  rw [hq0] at hprod
  have hdet : algebraMap R₀ S₀ (standardRulingPolynomial (F := K)) ≠ 0 := by
    intro hz
    apply standardRulingPolynomial_ne_zero (F := K)
    apply IsFractionRing.injective R₀ S₀
    simpa only [map_zero] using hz
  exact hdet (neg_eq_zero.mp (by simpa using hprod.symm))

end DimensionFourDependence
