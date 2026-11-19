import DimensionFourDependence.CoveringLineFamilyDimension
import DimensionFourDependence.LinePairParameters

/-! # Covering components from a point characterized by exact image relations

The covering construction uses only the point's exact polynomial image
relations. It therefore applies after an algebraic coefficient extension
without rebuilding an output-field presentation or geometric fiber.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

variable {K E : Type u} [Field K] [CharZero K] [Field E] [Algebra K E]

omit [CharZero K] in
/-- A relation-generic point is nonzero for an actual rank-three image. -/
theorem point_exact_image_relations_ne_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (O : Fin 4 → E)
    (hrel : ∀ P : MvPolynomial (Fin 4) K, aeval O P = 0 ↔ aeval H P = 0) : O ≠ 0 := by
  intro hz
  apply rank_three_polynomial_map_ne_zero H hrank
  funext i
  have hi := (hrel (X i)).mp (by rw [hz]; simp)
  simpa only [aeval_X, Pi.zero_apply] using hi

/-- Exact image relations identify the actual output field of the
point with the original rank-three image function field. -/
theorem point_exact_image_relations_output_field_trdeg_three
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (O : Fin 4 → E)
    (hrel : ∀ P : MvPolynomial (Fin 4) K, aeval O P = 0 ↔ aeval H P = 0) :
    Algebra.trdeg K (fullOutputField (K := K) O) = 3 := by
  have hideal : fiberVanishingIdeal (L := K) O = fiberVanishingIdeal (L := K)
      (fun i => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i)) := by
    rw [← imageRelationIdeal_eq_rational_relations]
    ext P
    exact hrel P
  have he := (outputFieldEquivOfRelations O
    (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i)) hideal).trdeg_eq
  exact he.trans ((polynomialOutputField_trdeg_eq_rank H).trans (by rw [hrank]; norm_num))

/-- A line through a point with exact actual image relations gives
the exact original image ideal as its component incidence kernel. -/
theorem relation_generic_line_component_incidence_kernel_eq_imageIdeal
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (O : Fin 4 → E)
    (hrel : ∀ P : MvPolynomial (Fin 4) K, aeval O P = 0 ↔ aeval H P = 0)
    (s : hypersurfaceLineAtlas (MvPolynomial.map (algebraMap K E) I.equation))
    (Q : Ideal (MvPolynomial LineMatrixIndex K))
    (heq : graphLineEquationIdeal (rename s.1.symm I.equation) ≤ Q)
    (hparameter : Q ≤ (extendedLineChartPrime (K := K) s.2.val).asIdeal)
    (hpoint : O ∈ hypersurfaceAtlasLine _ s) :
    RingHom.ker (componentLineIncidenceHom s.1 Q) = imageRelationIdeal H := by
  obtain ⟨u, hu⟩ := hypersurfaceAtlasLine_point_coordinates _ s O hpoint
  apply le_antisymm
  · intro P hP
    change componentLineIncidenceHom s.1 Q P = 0 at hP
    have he := componentLineIncidenceHom_evaluate s.1 s.2.val u Q hparameter P
    rw [hP, map_zero, ← hu] at he
    exact (hrel P).mp he.symm
  · rw [I.ideal_eq_span H hrank]
    apply Ideal.span_le.mpr
    intro P hP
    obtain rfl := Set.mem_singleton_iff.mp hP
    exact componentLineIncidenceHom_equation_zero I.equation s.1 Q heq

/-- A relation-generic actual line supplies a covering curve component
over the current coefficient field, with its dimension derived. -/
theorem relation_generic_line_exists_covering_curve_component
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (I : ImageRelationWitness H) (O : Fin 4 → E)
    (hrel : ∀ P : MvPolynomial (Fin 4) K, aeval O P = 0 ↔ aeval H P = 0)
    (s : hypersurfaceLineAtlas (MvPolynomial.map (algebraMap K E) I.equation))
    (hpoint : O ∈ hypersurfaceAtlasLine _ s) :
    ∃ Q ∈ (graphLineEquationIdeal (rename s.1.symm I.equation)).minimalPrimes,
      Q ≤ (extendedLineChartPrime (K := K) s.2.val).asIdeal ∧
      RingHom.ker (componentLineIncidenceHom s.1 Q) = imageRelationIdeal H ∧
      Algebra.trdeg K (FractionRing (MvPolynomial LineMatrixIndex K ⧸ Q)) = 1 := by
  obtain ⟨Q, hQ, hparameter⟩ := atlas_point_exists_original_field_component I.equation s
  let : Q.IsPrime := hQ.isPrime
  have hk := relation_generic_line_component_incidence_kernel_eq_imageIdeal
    H hrank I O hrel s Q hQ.le hparameter hpoint
  exact ⟨Q, hQ, hparameter, hk,
    covering_line_component_trdeg_one Q H hd hH hrank hind I s.1 hQ.le hk⟩

end DimensionFourDependence
