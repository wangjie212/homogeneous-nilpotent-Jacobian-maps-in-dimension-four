import DimensionFourDependence.HomogeneousProjectiveLine
import DimensionFourDependence.HypersurfaceLineAtlas
import DimensionFourDependence.IndependentGraphLines

/-! # Atlas points supplied by homogeneous affine line identities

An affine identity on an actual homogeneous equation gives a point of
its line atlas after scalar extension. Two independent directions modulo
the point give distinct represented lines and distinct atlas points.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}

/-- Evaluating a scalar-extended polynomial agrees with evaluating the
original equation in the coefficient algebra. -/
theorem aeval_map_algebra_extension
    {A : Type*} [CommRing A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    (R : MvPolynomial (Fin n) K) (x : Fin n → A) :
    aeval (R := E) x (MvPolynomial.map (algebraMap K E) R) = aeval (R := K) x R := by
  have hmaps : (algebraMap E A).comp (algebraMap K E) = algebraMap K A := by
    ext a
    exact (IsScalarTower.algebraMap_apply K E A a).symm
  simp only [aeval_def, eval₂_map, hmaps]

/-- An actual affine line identity supplies a representative of its
full projective line in the scalar-extended hypersurface line atlas. -/
theorem homogeneous_affine_line_exists_atlas_point [Infinite E]
    (R : MvPolynomial (Fin 4) K) {d : ℕ} (hR : R.IsHomogeneous d)
    (O D : Fin 4 → E) (hli : LinearIndependent E ![O, D])
    (hline : aeval (fun i => Polynomial.C (O i) + Polynomial.C (D i) * Polynomial.X) R = 0) :
    ∃ s : hypersurfaceLineAtlas (MvPolynomial.map (algebraMap K E) R),
      hypersurfaceAtlasLine _ s = Submodule.span E (Set.range ![O, D]) := by
  apply hypersurfaceLineAtlas_covers_all_lines
  · exact finrank_span_eq_card hli
  · intro x hx
    rw [aeval_map_algebra_extension]
    exact homogeneous_affine_line_span_contained R hR O D hline x hx

/-- Independence of a point and two directions supplies each line's independent pair. -/
theorem independent_triple_first_pairs
    (O D₁ D₂ : Fin 4 → E) (hli : LinearIndependent E ![O, D₁, D₂]) :
    LinearIndependent E ![O, D₁] ∧ LinearIndependent E ![O, D₂] := by
  constructor
  · have he : ![O, D₁, D₂] ∘ (![0, 1] : Fin 2 → Fin 3) = ![O, D₁] := by
      funext i
      fin_cases i <;> rfl
    rw [← he]
    exact hli.comp _ (by decide)
  · have he : ![O, D₁, D₂] ∘ (![0, 2] : Fin 2 → Fin 3) = ![O, D₂] := by
      funext i
      fin_cases i <;> rfl
    rw [← he]
    exact hli.comp _ (by decide)

/-- Two homogeneous affine line identities give distinct actual atlas
points representing distinct projective lines through their common point. -/
theorem two_homogeneous_affine_lines_atlas_points [Infinite E]
    (R : MvPolynomial (Fin 4) K) {d : ℕ} (hR : R.IsHomogeneous d)
    (O D₁ D₂ : Fin 4 → E) (hli : LinearIndependent E ![O, D₁, D₂])
    (hline₁ : aeval (fun i => Polynomial.C (O i) + Polynomial.C (D₁ i) * Polynomial.X) R = 0)
    (hline₂ : aeval (fun i => Polynomial.C (O i) + Polynomial.C (D₂ i) * Polynomial.X) R = 0) :
    ∃ s₁ s₂ : hypersurfaceLineAtlas (MvPolynomial.map (algebraMap K E) R),
      hypersurfaceAtlasLine _ s₁ = Submodule.span E (Set.range ![O, D₁]) ∧
      hypersurfaceAtlasLine _ s₂ = Submodule.span E (Set.range ![O, D₂]) ∧
      hypersurfaceAtlasLine _ s₁ ≠ hypersurfaceAtlasLine _ s₂ ∧ s₁ ≠ s₂ ∧
      O ∈ hypersurfaceAtlasLine _ s₁ ∧ O ∈ hypersurfaceAtlasLine _ s₂ := by
  obtain ⟨hpair₁, hpair₂⟩ := independent_triple_first_pairs O D₁ D₂ hli
  obtain ⟨s₁, hs₁⟩ := homogeneous_affine_line_exists_atlas_point R hR O D₁ hpair₁ hline₁
  obtain ⟨s₂, hs₂⟩ := homogeneous_affine_line_exists_atlas_point R hR O D₂ hpair₂ hline₂
  have hneq : hypersurfaceAtlasLine _ s₁ ≠ hypersurfaceAtlasLine _ s₂ := by
    rw [hs₁, hs₂]
    exact line_spans_distinct_of_independent_triple O D₁ D₂ hli
  refine ⟨s₁, s₂, hs₁, hs₂, hneq, ?_, ?_, ?_⟩
  · intro he
    exact hneq (congrArg (hypersurfaceAtlasLine _) he)
  · rw [hs₁]
    exact Submodule.subset_span ⟨0, rfl⟩
  · rw [hs₂]
    exact Submodule.subset_span ⟨0, rfl⟩

end DimensionFourDependence
