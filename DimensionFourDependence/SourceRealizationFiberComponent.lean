import DimensionFourDependence.ComponentSourceAlgebraicity
import DimensionFourDependence.FullOutputGeometricFiber
import DimensionFourDependence.GeometricFiberNonlinearity

/-! # An embedded source with algebraic constants gives an actual fiber component -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 2000000

variable {L E F G : Type*} [Field L] [Field E] [Field F] [Field G]
  [Algebra L F] [Algebra L E] [Algebra E G] [Algebra L G]
  [IsScalarTower L E G] {n : ℕ}

/-- A field embedding preserves the exact polynomial relation ideal. -/
theorem fiberVanishingIdeal_algHom (f : F →ₐ[L] G) (x : Fin n → F) :
    fiberVanishingIdeal (L := L) (f ∘ x) = fiberVanishingIdeal (L := L) x := by
  ext p
  change aeval (fun i => f (x i)) p = 0 ↔ aeval x p = 0
  rw [← comp_aeval_apply x f p]
  exact map_eq_zero_iff f f.injective

/-- Extending the constants algebraically makes the relations of an
embedded source point an actual minimal component of the original fiber. -/
theorem embedded_source_relations_form_geometric_component
    [Algebra.IsAlgebraic L E] (f : F →ₐ[L] G) (x : Fin n → F) :
    fiberVanishingIdeal (L := E) (f ∘ x) ∈
      (extendCoefficientIdeal E (fiberVanishingIdeal (L := L) x)).minimalPrimes := by
  have he := fiber_prime_minimal_after_algebraic_coefficients (L := L) (E := E) (f ∘ x)
  rwa [fiberVanishingIdeal_algHom f x] at he

/-- The generic coordinates of the exact prime of a point embed in
the point's field, retaining every coordinate and every constant. -/
theorem relation_prime_constructs_coordinate_embedding
    (P : Ideal (MvPolynomial (Fin n) E)) [P.IsPrime] (y : Fin n → G)
    (hP : fiberVanishingIdeal (L := E) y = P) :
    ∃ f : FractionRing (MvPolynomial (Fin n) E ⧸ P) →ₐ[E] G,
      ∀ i, f (primeQuotientCoordinate P i) = y i := by
  apply exists_fiber_embedding_of_relations_eq (primeQuotientCoordinate P) y
    (primeQuotientCoordinate_adjoin_eq_top P)
  rw [primeQuotientCoordinate_relations, hP]

/-- A specified minimal component embeds the original source field.
The ring-hom interface records the entire constant action explicitly,
so later changes of output base need no implicit scalar-action choices. -/
theorem minimal_component_constructs_source_ringHom
    (x : Fin n → F) (hx : IntermediateField.adjoin L (Set.range x) = ⊤)
    (P : Ideal (MvPolynomial (Fin n) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal (L := L) x)).minimalPrimes) :
    ∃ f : F →+* FractionRing (MvPolynomial (Fin n) E ⧸ P),
      (∀ i, f (x i) = primeQuotientCoordinate P i) ∧
      ∀ a : L, f (algebraMap L F a) =
        algebraMap E (FractionRing (MvPolynomial (Fin n) E ⧸ P)) (algebraMap L E a) := by
  obtain ⟨f, hf⟩ := exists_fiber_embedding_of_relations_eq x (primeQuotientCoordinate P) hx
    (componentGenericPoint_original_relations x P hP)
  refine ⟨f.toRingHom, hf, ?_⟩
  intro a
  exact (f.commutes a).trans (IsScalarTower.algebraMap_apply L E _ a)

omit [Algebra L F] [Algebra L E] [Algebra L G] [IsScalarTower L E G] in
/-- An invertible linear coordinate change over the constants carries
an affine line to an affine line and preserves its nonzero direction. -/
theorem LiesInAffineLine.mulVec
    (A B : Matrix (Fin n) (Fin n) E) (hBA : B * A = 1)
    (x : Fin n → G) (hx : LiesInAffineLine (E := E) x) :
    LiesInAffineLine (E := E) (A.map (algebraMap E G) *ᵥ x) := by
  classical
  obtain ⟨a, v, hv, t, hpos⟩ := hx
  refine ⟨A *ᵥ a, A *ᵥ v, ?_, t, ?_⟩
  · intro hz
    apply hv
    have he := congrArg (fun w => B *ᵥ w) hz
    simpa only [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec, Matrix.mulVec_zero] using he
  · intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
    simp_rw [hpos]
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]

end DimensionFourDependence
