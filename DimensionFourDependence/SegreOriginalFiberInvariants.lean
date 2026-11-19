import DimensionFourDependence.SegreOriginalOutputChart
import DimensionFourDependence.WeightedFiberInvariants

/-! # The three actual fiber invariants in the specified original Segre chart -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
attribute [local instance] coefficientFieldScalarTower

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The specified first three original polynomial outputs, in their
actual source fraction field. -/
noncomputable def segreOriginalOutputTriple (H : Fin 4 → MvPolynomial (Fin 4) K) : Fin 3 → S₀ :=
  fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)

/-- The last Segre output as an explicit rational function in the
original coefficient field, with no algebraic last-output choice. -/
noncomputable def segreOriginalCoefficientGraph (H : Fin 4 → MvPolynomial (Fin 4) K) :
    coefficientField (K := K) (segreOriginalOutputTriple H) :=
  segreGraphFunction (coefficientCoordinate (K := K) (segreOriginalOutputTriple H))

theorem segre_original_coefficient_graph_value
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hind : ¬ComponentsDependent H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0) :
    (segreOriginalCoefficientGraph H : S₀) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H 3) := by
  have he := segre_last_coordinate_eq_graph
    (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) (original_segre_first_output_ne_zero H hind)
    (by simpa only [map_sub, map_mul, map_zero] using congrArg (algebraMap (MvPolynomial (Fin 4) K) S₀) hSegre)
  exact he.symm

/-- In the original Segre chart, the first three outputs construct
all three actual coefficient invariants and their Euler weights.
No output permutation, graph function or coefficient data are supplied. -/
theorem exists_original_segre_weighted_fiber_invariants
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) (hSegre : H 0 * H 3 - H 1 * H 2 = 0) :
    ∃ (hY : AlgebraicIndependent K (segreOriginalOutputTriple H))
      (c q k : coefficientField (K := K) (segreOriginalOutputTriple H)),
      (c : S₀) = firstFiberInvariantInChart (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY (segreOriginalCoefficientGraph H) ∧
      (q : S₀) = secondFiberInvariant (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY (segreOriginalCoefficientGraph H) c ∧
      (k : S₀) = thirdFiberInvariant (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY (segreOriginalCoefficientGraph H) c q ∧
      coefficientEuler _ hY (segreOriginalCoefficientGraph H) = segreOriginalCoefficientGraph H ∧
      coefficientEuler _ hY c = algebraMap K _ ((d : K)⁻¹) * c ∧
      coefficientEuler _ hY q = algebraMap K _ (2 * (d : K)⁻¹ - 1) * q := by
  let Q : Fin 4 → S₀ := fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)
  let p := Equiv.refl (Fin 4)
  let Y := segreOriginalOutputTriple H
  let h := segreOriginalCoefficientGraph H
  have hY : AlgebraicIndependent K Y := original_segre_first_three_outputs_algebraicIndependent H hrank hind hSegre
  have hh : (h : S₀) = Q (p 3) := segre_original_coefficient_graph_value H hind hSegre
  have hNr : IsNilpotent (rationalJacobian Q) := by
    rw [rationalJacobian_polynomial]
    exact hN.map (algebraMap (MvPolynomial (Fin 4) K) S₀).mapMatrix
  have hr : (rationalJacobian Q).rank = 3 := by rw [rationalJacobian_polynomial]; exact hrank
  let c : coefficientField (K := K) Y := ⟨firstFiberInvariantInChart p Y hY h,
    firstFiberInvariantInChart_mem_of_rank_three Q hNr hr p hY h hh⟩
  have hc : (c : S₀) = firstFiberInvariantInChart p Y hY h := rfl
  let q : coefficientField (K := K) Y := ⟨secondFiberInvariant p Y hY h c,
    secondFiberInvariant_mem_of_nilpotent_rank_three Q hNr hr p hY h c hh hc⟩
  have hq : (q : S₀) = secondFiberInvariant p Y hY h c := rfl
  let k : coefficientField (K := K) Y := ⟨thirdFiberInvariant p Y hY h c q,
    thirdFiberInvariant_mem_of_nilpotent_rank_three Q hNr hr p hY h c q hh hc hq⟩
  refine ⟨hY, c, q, k, hc, hq, rfl, ?_, ?_, ?_⟩
  · exact homogeneous_last_output_euler H hd hH p hY h hh
  · exact firstFiberInvariant_output_weight H hd hH p hY h c hh hc
  · exact secondFiberInvariant_output_weight H hd hH p hY h c q hh hc hq

end DimensionFourDependence
