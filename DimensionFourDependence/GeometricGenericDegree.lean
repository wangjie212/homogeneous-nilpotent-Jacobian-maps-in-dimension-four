import DimensionFourDependence.FiberEmbedding
import DimensionFourDependence.AlgebraicCoefficientEmbedding

/-! # Passing the degree bound to every geometric generic-fiber component

The generic field of each component contains an embedded copy of the
original source field. Its algebraic coefficients land in the geometric
constants, giving the required coefficient embedding separately for
each component. No transitivity or geometric integrality is assumed.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {M L F E : Type*} [Field M] [Field L] [Field F] [Field E]
    [Algebra M L] [Algebra L F] [Algebra M F] [IsScalarTower M L F]
    [Algebra M E] [Algebra.IsAlgebraic M L] [Algebra.IsAlgebraic M E] [IsAlgClosed E]
    {n : ℕ}

/-- A degree bound over an algebraic coefficient subfield bounds every
component over algebraically closed algebraic generic constants. -/
theorem geometric_component_degree_of_algebraic_coefficients
    (x : Fin n → F) (hx : IntermediateField.adjoin M (Set.range x) = ⊤)
    (i : Fin n) (hi : Transcendental M (x i))
    (hupper : ∀ d ≥ 5, projectiveHilbertFunction (projectiveConeIdeal (L := L) x) d ≤ 6 * (d + 1))
    (P : Ideal (MvPolynomial (Fin n) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal (L := M) x)).minimalPrimes) :
    ∃ d : ℕ, d ≤ 6 ∧ HasCurveHilbertDegree
      (projectiveConeIdeal (L := E) (primeQuotientCoordinate P)) d := by
  let G := FractionRing (MvPolynomial (Fin n) E ⧸ P)
  let z := primeQuotientCoordinate P
  have hz : Transcendental E (z i) := componentGenericPoint_transcendental x P hP i hi
  obtain ⟨f, hf⟩ := exists_fiber_embedding_of_relations_eq x z hx
    (componentGenericPoint_original_relations x P hP)
  obtain ⟨g, hg⟩ := exists_algebraic_coefficient_embedding (L := L) (E := E) f
  let : Algebra L E := g.toRingHom.toAlgebra
  let fL : F →ₐ[L] G :=
    { f.toRingHom with
      commutes' a := by
        rw [IsScalarTower.algebraMap_apply L E G]
        exact (hg a).symm }
  have heval : (aeval z : MvPolynomial (Fin n) L →ₐ[L] G) = fL.comp (aeval x) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [aeval_X, AlgHom.comp_apply]
    change z j = f (x j)
    exact (hf j).symm
  have hrel : extendCoefficientIdeal E (fiberVanishingIdeal (L := L) x) ≤
      fiberVanishingIdeal (L := E) z := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change aeval z (MvPolynomial.map (algebraMap L E) p) = 0
    rw [aeval_map_coefficients, heval, AlgHom.comp_apply]
    change aeval x p = 0 at hp
    rw [hp, map_zero]
  have hcone := projectiveConeIdeal_extended_le x z hrel
  apply exists_curve_hilbert_degree_of_linear_bounds _ (projectiveConeIdeal_isHomogeneous z)
  · exact projectiveConeIdeal_hilbert_lower_bound z i hz
  · intro d hd
    calc
      projectiveHilbertFunction (projectiveConeIdeal (L := E) z) d ≤
          projectiveHilbertFunction (extendCoefficientIdeal E (projectiveConeIdeal (L := L) x)) d :=
        projectiveHilbertFunction_antitone hcone d
      _ = projectiveHilbertFunction (projectiveConeIdeal (L := L) x) d :=
        projectiveHilbertFunction_field_extension E _ d
      _ ≤ 6 * (d + 1) := hupper d hd

end DimensionFourDependence
