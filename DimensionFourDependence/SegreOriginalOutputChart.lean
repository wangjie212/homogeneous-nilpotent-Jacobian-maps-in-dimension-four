import DimensionFourDependence.SegreGraphDifferentials
import DimensionFourDependence.GraphLineGenericPointDensity
import DimensionFourDependence.OutputCoordinateFieldEquiv
import DimensionFourDependence.PrimitiveMapDegree

/-! # The original first three Segre outputs give the coefficient chart -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

universe u
variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- The original determinant identity solves for the last output in
the affine graph chart, with its original first-output denominator. -/
theorem segre_last_coordinate_eq_graph (Y : Fin 4 → F) (hY0 : Y 0 ≠ 0)
    (hquad : Y 0 * Y 3 - Y 1 * Y 2 = 0) :
    Y 3 = segreGraphFunction (fun i : Fin 3 => Y i.castSucc) := by
  apply (eq_div_iff hY0).mpr
  change Y 3 * Y 0 = Y 1 * Y 2
  simpa only [mul_comm] using sub_eq_zero.mp hquad

/-- The first three actual coordinates generate the entire Segre
output field; no independent-output selection or new source coordinates are used. -/
theorem segre_first_three_generate_output_field (Y : Fin 4 → F) (hY0 : Y 0 ≠ 0)
    (hquad : Y 0 * Y 3 - Y 1 * Y 2 = 0) :
    fullOutputField (K := K) (fun i : Fin 3 => Y i.castSucc) = fullOutputField (K := K) Y := by
  let E := fullOutputField (K := K) (fun i : Fin 3 => Y i.castSucc)
  have hmem (j : Fin 3) : Y j.castSucc ∈ E := IntermediateField.subset_adjoin K _ ⟨j, rfl⟩
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin K _ ⟨i.castSucc, rfl⟩
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun j => hmem j) i
    change Y 3 ∈ E
    rw [segre_last_coordinate_eq_graph Y hY0 hquad]
    exact E.div_mem (E.mul_mem (hmem 1) (hmem 2)) (hmem 0)

/-- Rank-three output dimension makes this specified Segre triple
algebraically independent, rather than merely selecting some output triple. -/
theorem segre_first_three_algebraicIndependent_of_output_dimension
    (Y : Fin 4 → F) (hY0 : Y 0 ≠ 0)
    (hquad : Y 0 * Y 3 - Y 1 * Y 2 = 0)
    (htr : Algebra.trdeg K (fullOutputField (K := K) Y) = 3) :
    AlgebraicIndependent K (fun i : Fin 3 => Y i.castSucc) := by
  apply algebraicIndependent_of_generatedField_trdeg_eq_card
  rwa [segre_first_three_generate_output_field Y hY0 hquad]

variable [CharZero K]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- Component independence makes the original first Segre output nonzero. -/
theorem original_segre_first_output_ne_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hind : ¬ComponentsDependent H) :
    algebraMap (MvPolynomial (Fin 4) K) S₀ (H 0) ≠ 0 := by
  have h0 : H 0 ≠ 0 := (linearIndependent_of_componentsIndependent H hind).ne_zero 0
  intro hz
  apply h0
  exact IsFractionRing.injective (MvPolynomial (Fin 4) K) S₀ (by simpa only [map_zero] using hz)

/-- The original rank-three Segre map constructs the paper's actual
first-three-output algebraic coefficient chart over the original field. -/
theorem original_segre_first_three_outputs_algebraicIndependent
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) (hSegre : H 0 * H 3 - H 1 * H 2 = 0) :
    AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) := by
  apply segre_first_three_algebraicIndependent_of_output_dimension
    (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) (original_segre_first_output_ne_zero H hind)
  · have he := congrArg (algebraMap (MvPolynomial (Fin 4) K) S₀) hSegre
    simpa only [map_sub, map_mul, map_zero] using he
  · exact (polynomialOutputField_trdeg_eq_rank H).trans (by rw [hrank]; norm_num)

end DimensionFourDependence
