import DimensionFourDependence.RelationGenericCoveringComponent
import DimensionFourDependence.NondevelopableImageQuadric

/-! # The geometric quadric argument from exact relations and normal rigidity

The geometric argument uses exact image relations of the common point
and independence of the four actual normal polynomials. These data give
covering curves, exclude their concurrence, and propagate the actual
pair incidence to the component product. They suffice without a chosen
presentation of the output field over the current coefficient field.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

section Families

variable {K : Type*} [Field K] [IsAlgClosed K]
variable (Q : Ideal (MvPolynomial LineMatrixIndex K)) [Q.IsPrime]

/-- Independence of the actual normal polynomials excludes concurrence
of an actual covering family over the current coefficient field. -/
theorem covering_line_component_not_concurrent_of_normal_independent
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (hNormal : ¬ ComponentsDependent (imageRelationNormal H I.equation))
    (p : Equiv.Perm (Fin 4))
    (heq : graphLineEquationIdeal (rename p.symm I.equation) ≤ Q)
    (hk : RingHom.ker (componentLineIncidenceHom p Q) = imageRelationIdeal H) :
    ¬ ∃ T : Submodule K (Fin 4 → K), finrank K T = 1 ∧
      ∀ B : lineComponentPoints Q, T ≤ lineChartMemberLine p B.val := by
  rintro ⟨T, hT, hcontain⟩
  obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := K) (M := T)).mp
    (show 0 < finrank K T by rw [hT]; omega)
  have hv0 : (v : Fin 4 → K) ≠ 0 := fun hz => hv (Subtype.ext hz)
  have hn := covering_line_component_common_vertex_normal_relation Q H I p heq hk v
    (fun B hB => hcontain ⟨B, hB⟩ v.property)
  apply hNormal
  refine ⟨v, hv0, ?_⟩
  simpa only [MvPolynomial.smul_eq_C_mul] using hn

/-- A covering component with independent actual image and normal
components has three actual skew members. -/
theorem normal_independent_covering_component_skew_triple
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hind : ¬ ComponentsDependent H)
    (I : ImageRelationWitness H) (hNormal : ¬ ComponentsDependent (imageRelationNormal H I.equation))
    (p : Equiv.Perm (Fin 4))
    (heq : graphLineEquationIdeal (rename p.symm I.equation) ≤ Q)
    (hk : RingHom.ker (componentLineIncidenceHom p Q) = imageRelationIdeal H) :
    ∃ B ∈ lineComponentPoints Q, ∃ D ∈ lineComponentPoints Q, ∃ T ∈ lineComponentPoints Q,
      Disjoint (lineChartMemberLine p B) (lineChartMemberLine p D) ∧
      Disjoint (lineChartMemberLine p B) (lineChartMemberLine p T) ∧
      Disjoint (lineChartMemberLine p D) (lineChartMemberLine p T) := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) K) := graphLineChartTopology K
  let : IrreducibleSpace (lineComponentPoints Q) :=
    Subtype.irreducibleSpace (lineComponentPoints_isIrreducible Q)
  obtain ⟨a, _, b, _, c, _, hab, hac, hbc⟩ :=
    noncoplanar_nonconcurrent_irreducible_family_skew_triple
      (fun B : lineComponentPoints Q => lineChartMemberLine p B.val)
      (fun B => lineChartMemberLine_finrank p B.val)
      (fun B => lineChartMemberLine_subfamily_skew_isOpen _ p B)
      (covering_line_component_not_coplanar Q H hind p hk)
      (covering_line_component_not_concurrent_of_normal_independent Q H I hNormal p heq hk)
      Set.univ isOpen_univ Set.univ_nonempty
  exact ⟨a.val, a.property, b.val, b.property, c.val, c.property, hab, hac, hbc⟩

end Families

universe u

variable {K E : Type u} [Field K] [CharZero K] [IsAlgClosed K] [Field E] [Algebra K E]

/-- Two distinct contained lines through a point with exact image
relations, together with independence of the actual normal components,
give the smooth determinant quadric in the current coefficient field. -/
theorem relation_generic_distinct_lines_quadric_of_normal_independent
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (I : ImageRelationWitness H) (hNormal : ¬ ComponentsDependent (imageRelationNormal H I.equation))
    (O : Fin 4 → E)
    (hrel : ∀ P : MvPolynomial (Fin 4) K, aeval O P = 0 ↔ aeval H P = 0)
    (s t : hypersurfaceLineAtlas (MvPolynomial.map (algebraMap K E) I.equation))
    (hs : O ∈ hypersurfaceAtlasLine _ s) (ht : O ∈ hypersurfaceAtlasLine _ t)
    (hne : hypersurfaceAtlasLine _ s ≠ hypersurfaceAtlasLine _ t) :
    I.degree = 2 ∧
      (∀ x : Fin 4 → K, x ≠ 0 → (fun i => aeval x (pderiv i I.equation)) ≠ 0) ∧
      ∃ (e : (Fin 4 → K) ≃ₗ[K] ((Fin 2 → K) × (Fin 2 → K))) (c : K), c ≠ 0 ∧
        rulingPolynomialInCoordinates e = MvPolynomial.C c * I.equation ∧
        ∀ x : Fin 4 → K, aeval x I.equation = 0 ↔ standardRulingQuadric (e x) = 0 := by
  obtain ⟨Q, hQ, hB, hk, hQdim⟩ :=
    relation_generic_line_exists_covering_curve_component H hd hH hrank hind I O hrel s hs
  obtain ⟨Q', hQ', hD, hk', hQ'dim⟩ :=
    relation_generic_line_exists_covering_curve_component H hd hH hrank hind I O hrel t ht
  let : Q.IsPrime := hQ.isPrime
  let : Q'.IsPrime := hQ'.isPrime
  have hO := point_exact_image_relations_ne_zero H hrank O hrel
  have hdim := distinct_line_pair_generated_field_trdeg_ge_two s.1 t.1 s.2.val t.2.val O hO hs ht hne
    (point_exact_image_relations_output_field_trdeg_three H hrank O hrel)
  have hmeet : ¬ Disjoint (lineChartMemberLine s.1 s.2.val) (lineChartMemberLine t.1 t.2.val) := by
    intro h
    exact hO (Submodule.disjoint_def.mp h O hs ht)
  have hinc := two_dimensional_incident_pair_forces_component_incidence Q Q' hQdim hQ'dim
    s.1 t.1 s.2.val t.2.val hB hD hdim hmeet
  obtain ⟨B, hBS, D, hDS, T, hTS, hBD, hBT, hDT⟩ :=
    normal_independent_covering_component_skew_triple Q H hind I hNormal s.1 hQ.le hk
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) K) := graphLineChartTopology K
  let : Nonempty (lineComponentPoints Q') := (lineComponentPoints_isIrreducible Q').nonempty.to_subtype
  have hquad : I.degree = 2 ∧
      ∃ e : (Fin 4 → K) ≃ₗ[K] ((Fin 2 → K) × (Fin 2 → K)),
        ∀ x : Fin 4 → K, aeval x I.equation = 0 ↔ standardRulingQuadric (e x) = 0 := by
    apply covering_transversals_identify_actual_image_quadric Q' H hd hH hrank hind I t.1 hk'
      (lineChartMemberLine s.1 B) (lineChartMemberLine s.1 D) (lineChartMemberLine s.1 T)
      (lineChartMemberLine_finrank s.1 B) (lineChartMemberLine_finrank s.1 D)
      (lineChartMemberLine_finrank s.1 T) hBD hBT hDT Set.univ isOpen_univ Set.univ_nonempty
    intro C _
    exact ⟨fun h => hinc ⟨B, hBS⟩ C h.symm, fun h => hinc ⟨D, hDS⟩ C h.symm,
      fun h => hinc ⟨T, hTS⟩ C h.symm⟩
  obtain ⟨hdeg, e, hzero⟩ := hquad
  obtain ⟨c, hc, he⟩ := I.ruling_polynomial_scalar_multiple_of_zero_set H hd hH hrank hind e hzero
  exact ⟨hdeg, fun x hx => polynomial_associated_ruling_projectively_nonsingular I.equation e c he x hx,
    e, c, hc, he, hzero⟩

end DimensionFourDependence
