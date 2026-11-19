import DimensionFourDependence.GeneratedFieldDimension
import DimensionFourDependence.LinePairIncidenceMatrix

/-! # A point of full relative dimension is generic on its actual graph line

Two graph coordinates generate all four point coordinates. If the point's
generated field has dimension two, evaluation at those two coordinates
is injective by dimension drop. Thus every polynomial relation of the
point vanishes identically on the original graph line.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

variable {K E : Type u} [Field K] [Field E] [Algebra K E]

/-- A finite generating family retaining its full possible
transcendence degree is algebraically independent. -/
theorem algebraicIndependent_of_generatedField_trdeg_eq_card {n : ℕ}
    (x : Fin n → E) (hdim : Algebra.trdeg K (fullOutputField (K := K) x) = n) :
    AlgebraicIndependent K x := by
  let f : MvPolynomial (Fin n) K →ₐ[K] E := aeval x
  have hpoly : Algebra.trdeg K (MvPolynomial (Fin n) K) = n := by
    simp [MvPolynomial.trdeg_of_isDomain]
  have hrange : Algebra.trdeg K f.range = n := by
    rw [show f.range = Algebra.adjoin K (Set.range x) from
      (Algebra.adjoin_range_eq_range_aeval K x).symm]
    rw [← generatedField_trdeg_eq_generatedAlgebra]
    exact hdim
  have hinj := surjective_algHom_injective_of_trdeg_eq f.rangeRestrict f.rangeRestrict_surjective
    (hpoly ▸ (by simp)) (hpoly.trans hrange.symm)
  apply algebraicIndependent_iff_injective_aeval.mpr
  intro p q hpq
  exact hinj (Subtype.ext hpq)

/-- Evaluation at the two actual graph parameters commutes with
coefficient extension and with the original coordinate permutation. -/
theorem graphLineRestriction_eval_extension
    (p : Equiv.Perm (Fin 4)) (B : Matrix (Fin 2) (Fin 2) K)
    (u : Fin 2 → E) (P : MvPolynomial (Fin 4) K) :
    aeval u (graphLineRestriction B (rename p.symm P)) =
      aeval (fun i => (![u 0, u 1, (B.map (algebraMap K E) *ᵥ u) 0,
        (B.map (algebraMap K E) *ᵥ u) 1]) (p.symm i)) P := by
  unfold graphLineRestriction
  rw [comp_aeval_apply]
  have he : (fun i => aeval u (graphLineCoordinate B i)) =
      ![u 0, u 1, (B.map (algebraMap K E) *ᵥ u) 0,
        (B.map (algebraMap K E) *ᵥ u) 1] := by
    funext i
    fin_cases i <;> simp [graphLineCoordinate, Matrix.mulVec, dotProduct]
  rw [he, aeval_rename]
  rfl

/-- A point retaining dimension two on a coefficient-extended graph
line has no polynomial relations beyond those of that original line. -/
theorem graph_line_generic_point_polynomial_density
    (p : Equiv.Perm (Fin 4)) (B : Matrix (Fin 2) (Fin 2) K) (Q : Fin 4 → E)
    (hQ : Q ∈ lineChartMemberLine p (B.map (algebraMap K E)))
    (hdim : Algebra.trdeg K (fullOutputField (K := K) Q) = 2) :
    ∀ P : MvPolynomial (Fin 4) K, aeval Q P = 0 →
      ∀ x ∈ lineChartMemberLine p B, aeval x P = 0 := by
  obtain ⟨z, hz, hzQ⟩ := hQ
  obtain ⟨u, hu⟩ := (mem_graphLineFour _ _).mp hz
  have hQcoord : Q = fun i => (![u 0, u 1,
      (B.map (algebraMap K E) *ᵥ u) 0, (B.map (algebraMap K E) *ᵥ u) 1]) (p.symm i) := by
    rw [← hzQ, hu]
    rfl
  let U := fullOutputField (K := K) u
  have hu0 : u 0 ∈ U := IntermediateField.subset_adjoin K _ ⟨0, rfl⟩
  have hu1 : u 1 ∈ U := IntermediateField.subset_adjoin K _ ⟨1, rfl⟩
  have hQmem : ∀ i, Q i ∈ U := by
    intro i
    rw [hQcoord]
    dsimp only
    generalize p.symm i = j
    fin_cases j
    · exact hu0
    · exact hu1
    · change (B.map (algebraMap K E) *ᵥ u) 0 ∈ U
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
      exact U.add_mem (U.mul_mem (U.algebraMap_mem _) hu0) (U.mul_mem (U.algebraMap_mem _) hu1)
    · change (B.map (algebraMap K E) *ᵥ u) 1 ∈ U
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
      exact U.add_mem (U.mul_mem (U.algebraMap_mem _) hu0) (U.mul_mem (U.algebraMap_mem _) hu1)
  have hle : fullOutputField (K := K) Q ≤ U := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact hQmem i
  have hl : 2 ≤ Algebra.trdeg K U := by
    rw [← hdim]
    exact trdeg_le_of_injective (IntermediateField.inclusion hle) (IntermediateField.inclusion hle).injective
  let f : MvPolynomial (Fin 2) K →ₐ[K] E := aeval u
  have hpoly : Algebra.trdeg K (MvPolynomial (Fin 2) K) = 2 := by
    simp [MvPolynomial.trdeg_of_isDomain]
  have hbound := trdeg_le_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hrange : f.range = Algebra.adjoin K (Set.range u) :=
    (Algebra.adjoin_range_eq_range_aeval K u).symm
  rw [hrange, ← generatedField_trdeg_eq_generatedAlgebra, hpoly] at hbound
  have huind : AlgebraicIndependent K u :=
    algebraicIndependent_of_generatedField_trdeg_eq_card u (le_antisymm hbound hl)
  intro P hP
  have he : aeval u (graphLineRestriction B (rename p.symm P)) = 0 := by
    rw [graphLineRestriction_eval_extension, ← hQcoord, hP]
  have hrestrict : graphLineRestriction B (rename p.symm P) = 0 :=
    huind (by simpa only [map_zero] using he)
  exact hypersurfaceAtlasLine_contained P ⟨p, ⟨B, hrestrict⟩⟩

end DimensionFourDependence
