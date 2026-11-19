import DimensionFourDependence.FixedLastFiberEquations
import DimensionFourDependence.FullOutputGeometricFiber

/-! # Each actual geometric component has a nonzero constant final coordinate -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 105000

variable {K : Type u} [Field K] [CharZero K]
local notation "F" => FractionRing (MvPolynomial (Fin 4) K)
local notation "x" => (rationalCoordinate (K := K) (n := 4))

/-- Any independent output chart gives the compatible inclusion of its
actual coefficient field in each geometric component's constants. -/
theorem full_output_independent_chart_geometric_coefficient_embedding
    (H : Fin 4 → F) (hrank : (rationalJacobian H).rank = 3) (p : Equiv.Perm (Fin 4))
    (hp : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
    (E : Type u) [Field E] [Algebra (fullOutputField (K := K) H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal (L := fullOutputField (K := K) H) x)).minimalPrimes) :
    let M := fullOutputField (K := K) H
    let L := coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc))
    letI := fullOutputCoefficientAlgebra H hrank p hp
    ∃ f : F →ₐ[M] FractionRing (MvPolynomial (Fin 4) E ⧸ P),
      (∀ i, f (x i) = primeQuotientCoordinate P i) ∧
      ∃ g : L →ₐ[M] E, ∀ l : L,
        algebraMap E (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (g l) = f (algebraMap L F l) := by
  let M := fullOutputField (K := K) H
  let L := coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc))
  let : Algebra M L := fullOutputCoefficientAlgebra H hrank p hp
  let : IsScalarTower M L F := IsScalarTower.of_algebraMap_eq (R := M) (S := L) (A := F) (fun _ => rfl)
  let : Algebra.IsAlgebraic M L := fullOutputCoefficient_isAlgebraic H hrank p hp
  obtain ⟨f, hf⟩ := exists_fiber_embedding_of_relations_eq x (primeQuotientCoordinate P)
    (rationalSource_adjoin_coordinates_eq_top M) (componentGenericPoint_original_relations x P hP)
  obtain ⟨g, hg⟩ := exists_algebraic_coefficient_embedding (L := L) (E := E) f
  exact ⟨f, hf, g, hg⟩

/-- The fixed last value is a nonzero scalar on every geometric
component, represented by a literal affine equation in its prime ideal. -/
theorem fixed_last_geometric_component_has_nonzero_last_value
    (H : Fin 4 → F) (W : FixedLastFiberEquations H) (hr : (rationalJacobian H).rank = 3)
    (E : Type u) [Field E] [Algebra (fullOutputField (K := K) H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal (L := fullOutputField (K := K) H) x)).minimalPrimes) :
    ∃ c : E, c ≠ 0 ∧ X (Fin.last 3) - C c ∈ P := by
  let M := fullOutputField (K := K) H
  let L := coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc))
  let : Algebra M L := fullOutputCoefficientAlgebra H hr W.chart W.independent
  obtain ⟨f, hf, g, hg⟩ := full_output_independent_chart_geometric_coefficient_embedding H hr W.chart W.independent E P hP
  let c := g W.lastValue
  have hc : c ≠ 0 := fun hz => W.lastValue_ne_zero (g.injective (hz.trans (map_zero g).symm))
  refine ⟨c, hc, ?_⟩
  rw [← primeQuotientCoordinate_relations P]
  change aeval (primeQuotientCoordinate P) (X (Fin.last 3) - C c) = 0
  simp only [map_sub, aeval_X, aeval_C]
  rw [hg W.lastValue]
  have h := congrArg f W.lastValue_eq
  rw [hf (Fin.last 3)] at h
  exact sub_eq_zero.mpr h.symm

end DimensionFourDependence
