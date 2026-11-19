import DimensionFourDependence.GeometricGenericDegree
import DimensionFourDependence.GeometricHilbertBound

/-! # Every actual geometric generic component has degree at most the original fiber -/

namespace DimensionFourDependence

open MvPolynomial

variable {M L F E : Type*} [Field M] [Field L] [Field F] [Field E]
  [Algebra M L] [Algebra L F] [Algebra M F] [IsScalarTower M L F]
  [Algebra M E] [Algebra.IsAlgebraic M L] [Algebra.IsAlgebraic M E] [IsAlgClosed E]
  {n : ℕ}

/-- The actual source embedding and coefficient embedding place
each geometric generic component inside the same extended original
fiber. Its degree therefore obeys every original fiber degree bound,
including the simple-root bound two. -/
theorem geometric_generic_component_curve_degree_le_original
    (x : Fin n → F) (hx : IntermediateField.adjoin M (Set.range x) = ⊤)
    (P : Ideal (MvPolynomial (Fin n) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal (L := M) x)).minimalPrimes)
    {D D' : ℕ} (hD : HasCurveHilbertDegree (projectiveConeIdeal (L := L) x) D)
    (hD' : HasCurveHilbertDegree (projectiveConeIdeal (L := E) (primeQuotientCoordinate P)) D') :
    D' ≤ D := by
  let G := FractionRing (MvPolynomial (Fin n) E ⧸ P)
  let z := primeQuotientCoordinate P
  obtain ⟨f, hf⟩ := exists_fiber_embedding_of_relations_eq x z hx
    (componentGenericPoint_original_relations x P hP)
  obtain ⟨g, hg⟩ := exists_algebraic_coefficient_embedding (L := L) (E := E) f
  letI : Algebra L E := g.toRingHom.toAlgebra
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
  exact curveHilbertDegree_le_of_ideal_le (projectiveConeIdeal_extended_le x z hrel)
    (curveHilbertDegree_field_extension E _ D hD) hD'

end DimensionFourDependence
