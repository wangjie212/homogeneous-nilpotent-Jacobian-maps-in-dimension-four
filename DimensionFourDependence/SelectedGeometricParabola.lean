import DimensionFourDependence.FullOutputGeometricFiber
import DimensionFourDependence.ParabolaFieldEmbedding

/-! # Original parabolas on the actual full-output geometric components

The coefficient embedding is constructed for any specified independent
output chart. Thus a parabola constructed by the developable calculation
passes to every nonlinear geometric generic component, retaining the
entire component ideal and its smooth polynomial coordinate algebra.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

/-- Every selected independent chart supplies compatible source and
coefficient embeddings into each actual full-output geometric component. -/
theorem selected_full_output_geometric_coefficient_embedding
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hrank : (rationalJacobian H).rank = 3) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
    (E : Type*) [Field E] [Algebra (fullOutputField (K := K) H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := fullOutputField (K := K) H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) :
    let M := fullOutputField (K := K) H
    let L := coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc))
    letI := fullOutputCoefficientAlgebra H hrank p hY
    ∃ f : FractionRing (MvPolynomial (Fin 4) K) →ₐ[M]
        FractionRing (MvPolynomial (Fin 4) E ⧸ P),
      (∀ i, f (rationalCoordinate (K := K) i) = primeQuotientCoordinate P i) ∧
      ∃ g : L →ₐ[M] E, ∀ l : L,
        algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (g l) =
          f (algebraMap L (FractionRing (MvPolynomial (Fin 4) K)) l) := by
  let M := fullOutputField (K := K) H
  let L := coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc))
  let : Algebra M L := fullOutputCoefficientAlgebra H hrank p hY
  let : IsScalarTower M L (FractionRing (MvPolynomial (Fin 4) K)) :=
    IsScalarTower.of_algebraMap_eq (R := M) (S := L)
      (A := FractionRing (MvPolynomial (Fin 4) K)) (by intro a; rfl)
  let : Algebra.IsAlgebraic M L := fullOutputCoefficient_isAlgebraic H hrank p hY
  obtain ⟨f, hf⟩ := exists_fiber_embedding_of_relations_eq
    (rationalCoordinate (K := K) (n := 4)) (primeQuotientCoordinate P)
    (rationalSource_adjoin_coordinates_eq_top M)
    (componentGenericPoint_original_relations (rationalCoordinate (K := K) (n := 4)) P hP)
  obtain ⟨g, hg⟩ := exists_algebraic_coefficient_embedding (L := L) (E := E) f
  exact ⟨f, hf, g, hg⟩

/-- Nonlinearity on a geometric component also gives nonlinearity
over any specified actual independent-chart coefficient field. -/
theorem selected_geometric_component_nonlinear_implies_actual_nonlinear
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hrank : (rationalJacobian H).rank = 3) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
    (E : Type*) [Field E] [Algebra (fullOutputField (K := K) H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := fullOutputField (K := K) H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    ¬ LiesInAffineLine
      (E := coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)))
      (rationalCoordinate (K := K) (n := 4)) := by
  let := fullOutputCoefficientAlgebra H hrank p hY
  obtain ⟨f, hf, g, hg⟩ := selected_full_output_geometric_coefficient_embedding H hrank p hY E P hP
  intro hx
  apply hline
  have hm := LiesInAffineLine.map_of_compatible f.toRingHom g.toRingHom hg
    (rationalCoordinate (K := K) (n := 4)) hx
  have he : f.toRingHom ∘ rationalCoordinate (K := K) (n := 4) = primeQuotientCoordinate P :=
    funext hf
  rwa [he] at hm

/-- The parabola in the original four source coordinates transfers
to every actual nonlinear full-output geometric generic component. -/
theorem selected_geometric_component_parabola_of_actual_parabola
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hrank : (rationalJacobian H).rank = 3) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
    (hx : LiesInAffineParabola
      (L := coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)))
      (rationalCoordinate (K := K) (n := 4)))
    (E : Type*) [Field E] [Algebra (fullOutputField (K := K) H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := fullOutputField (K := K) H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    LiesInAffineParabola (L := E) (primeQuotientCoordinate P) := by
  let := fullOutputCoefficientAlgebra H hrank p hY
  obtain ⟨f, hf, g, hg⟩ := selected_full_output_geometric_coefficient_embedding H hrank p hY E P hP
  have he : f.toRingHom ∘ rationalCoordinate (K := K) (n := 4) = primeQuotientCoordinate P :=
    funext hf
  have hline' : ¬ LiesInAffineLine (E := E)
      (f.toRingHom ∘ rationalCoordinate (K := K) (n := 4)) := by rwa [he]
  have hm := LiesInAffineParabola.map_of_compatible_of_nonlinear f.toRingHom g.toRingHom hg
    (rationalCoordinate (K := K) (n := 4)) hx hline'
  rwa [he] at hm

/-- The entire actual component coordinate quotient is a polynomial
algebra and is smooth, without replacing its ideal by support data. -/
theorem geometric_parabola_component_polynomial_and_smooth
    (E : Type*) [Field E] (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hx : LiesInAffineParabola (L := E) (primeQuotientCoordinate P)) :
    Nonempty (Polynomial E ≃ₐ[E] (MvPolynomial (Fin 4) E ⧸ P)) ∧
      Algebra.Smooth E (MvPolynomial (Fin 4) E ⧸ P) := by
  have he := parabola_coordinate_quotient_polynomial_equiv (primeQuotientCoordinate P) hx
  have hs := parabola_coordinate_quotient_smooth (primeQuotientCoordinate P) hx
  rw [primeQuotientCoordinate_relations] at he hs
  exact ⟨he, hs⟩

end DimensionFourDependence
