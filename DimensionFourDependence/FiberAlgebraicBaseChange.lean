import DimensionFourDependence.GeometricHilbertBound

/-! # The selected fiber prime is a component after adjoining algebraic constants

The prime relation ideal contracts to the original relation ideal. In an
integral coefficient extension, incomparability of primes then makes it a
minimal prime over the scalar-extended original ideal.
-/

namespace DimensionFourDependence

/-- A prime in an integral extension is minimal over the extension of its contraction. -/
theorem prime_minimal_over_integral_extension {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (P : Ideal R) (Q : Ideal S) [Q.IsPrime]
    (hQ : Q.comap f = P) : Q ∈ (P.map f).minimalPrimes := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  have hmap : P.map f ≤ Q := Ideal.map_le_iff_le_comap.mpr hQ.ge
  refine ⟨⟨inferInstance, hmap⟩, ?_⟩
  intro J hJ hJQ
  have : J.IsPrime := hJ.1
  have hcomp : J.comap f = P := by
    apply le_antisymm
    · exact (Ideal.comap_mono hJQ).trans_eq hQ
    · exact Ideal.map_le_iff_le_comap.mp hJ.2
  by_contra hQJ
  have hne : J ≠ Q := fun he => hQJ he.symm.le
  have hlt := Ideal.IsIntegral.under_lt_under (R := R) (lt_of_le_of_ne hJQ hne)
  change J.comap f < Q.comap f at hlt
  rw [hcomp, hQ] at hlt
  exact lt_irrefl _ hlt

open MvPolynomial

variable {L E F : Type*} [Field L] [Field E] [Field F]
    [Algebra L E] [Algebra E F] [Algebra L F] [IsScalarTower L E F] {n : ℕ}

/-- Relations over the larger coefficient field contract to the original relations. -/
theorem fiberVanishingIdeal_comap_coefficients (x : Fin n → F) :
    (fiberVanishingIdeal (L := E) x).comap (MvPolynomial.map (algebraMap L E)) =
      fiberVanishingIdeal (L := L) x := by
  ext p
  change MvPolynomial.eval₂ (algebraMap E F) x (MvPolynomial.map (algebraMap L E) p) = 0 ↔
    MvPolynomial.eval₂ (algebraMap L F) x p = 0
  rw [MvPolynomial.eval₂_map, ← IsScalarTower.algebraMap_eq L E F]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- For an algebraic extension of coefficient fields, the actual prime
of the selected generic point is a minimal prime over the extended fiber ideal. -/
theorem fiber_prime_minimal_after_algebraic_coefficients [Algebra.IsAlgebraic L E]
    (x : Fin n → F) :
    fiberVanishingIdeal (L := E) x ∈
      (extendCoefficientIdeal E (fiberVanishingIdeal (L := L) x)).minimalPrimes := by
  apply prime_minimal_over_integral_extension (MvPolynomial.map (algebraMap L E))
    _ _ _ (fiberVanishingIdeal_comap_coefficients x)
  rw [← MvPolynomial.algebraMap_def]
  exact algebraMap_isIntegral_iff.mpr inferInstance

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- The actual fiber prime over the relative algebraic closure is a
component of the original projected fiber after extending the three-output field. -/
theorem fiber_witness_prime_component_after_constants
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (W : FiberEquationWitness H) :
    fiberVanishingIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc)))
      (fun i : Fin 3 => rationalCoordinate (K := K) (W.chart i.castSucc)) ∈
    (extendCoefficientIdeal
      (coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc)))
      (fiberVanishingIdeal
        (L := IntermediateField.adjoin K (Set.range (fun i : Fin 3 => H (W.chart i.castSucc))))
        (fun i : Fin 3 => rationalCoordinate (K := K) (W.chart i.castSucc)))).minimalPrimes := by
  exact fiber_prime_minimal_after_algebraic_coefficients _

end DimensionFourDependence
