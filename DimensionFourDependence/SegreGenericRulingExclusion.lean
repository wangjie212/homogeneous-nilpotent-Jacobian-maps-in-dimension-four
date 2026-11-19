import DimensionFourDependence.SegreOriginalRulingExclusion
import DimensionFourDependence.HomogeneousProjectiveSubstitution

/-! # A ruling-preserving primitive boundary direction is not the image generic point -/

namespace DimensionFourDependence

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option quotPrecheck false

universe u
variable {K κ : Type u} [Field K] [CharZero K] [Field κ] [Algebra K κ]

/-- A generic original Segre direction cannot map to a generic
original target with either ruling parameter unchanged. Actual
projective dominance and the forbidden polynomial ruling relation
are constructed from the generic source, target and cross equations. -/
theorem no_generic_original_segre_direction_with_same_ruling_target
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0) (hH0 : H ≠ 0)
    (G : MvPolynomial (Fin 4) K) (hG : G ≠ 0) (c : ℕ) (hGh : G.IsHomogeneous c)
    (P : Fin 4 → MvPolynomial (Fin 4) K) {m : ℕ} (hm : 0 < m)
    (hP : IsHomogMap P m) (hprim : IsPrimitiveVec P)
    (hHP : H = fun i => G * P i) (hcm : c + m = d)
    (b y : Fin 4 → κ) (hb : b ≠ 0) (hy : y ≠ 0)
    (hbgen : projectiveFieldPoint (E := K) b hb = projectiveImageGenericPoint H hd hH hH0)
    (hygen : projectiveFieldPoint (E := K) y hy = projectiveImageGenericPoint H hd hH hH0)
    (hcross : ∀ i j, y i * aeval b (P j) - y j * aeval b (P i) = 0)
    (r : Fin 4) (hr : r = 1 ∨ r = 2) (hruling : y 0 * b r - y r * b 0 = 0) : False := by
  have hPb := primitive_part_defined_at_projective_generic_point H hd hH hH0 hrank I P hP hprim b hb hbgen
  obtain ⟨a, ha, hby⟩ := nonzero_vectors_proportional_of_cross_equations _ _ hy hPb hcross
  have hdom := generic_source_and_target_construct_projective_restriction_dominance H hd hH hH0 hrank I
    P hm hP hprim b y hb hy hbgen hygen a ha hby
  let Q := segreOriginalSourceDeterminantPrime H hd hH hrank hind I hSegre
  let z : MvPolynomial (Fin 4) K := P r * X 0 - P 0 * X r
  have hz : z.IsHomogeneous (m + 1) :=
    ((hP r).mul (isHomogeneous_X (R := K) 0)).sub ((hP 0).mul (isHomogeneous_X (R := K) r))
  have hzb : aeval b z = 0 := by
    simp only [z, map_sub, map_mul, aeval_X, hby]
    linear_combination -a * hruling
  have hzmem := (projectiveFieldPoint_homogeneous_mem b hb z hz).mpr hzb
  rw [hbgen] at hzmem
  have hQ : z ∈ Q.asIdeal := by
    rw [← original_segre_image_relation_ideal_eq_determinant_prime H hd hH hrank hind I hSegre]
    exact hzmem
  have hno := lemma_5_2_segre_cross_relations H hd hH hrank hind I hSegre
    hN hH0 G hG c hGh P hm hP hprim hHP hcm hdom
  rcases hr with rfl | rfl
  · exact hno.2 hQ
  · exact hno.1 hQ

end DimensionFourDependence
