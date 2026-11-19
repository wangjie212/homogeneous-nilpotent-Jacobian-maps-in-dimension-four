import DimensionFourDependence.GenericFiberOutput
import DimensionFourDependence.CoprimeBaseGenericAvoidance

/-! # Actual geometric generic fibers avoid original coprime base loci

Every point of an actual component's entire affine zero locus evaluates
the original map to its generic output. Three independent output values
then rule out a common zero of any original coprime polynomial pair.
This supplies the dimension argument without assuming base-locus
avoidance or replacing the generic component by a chosen open subset.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K]
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    (E : Type*) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

include hP

/-- Each original output equation belongs to the entire actual
geometric component ideal. -/
theorem geometric_component_original_output_relation (i : Fin 4) :
    MvPolynomial.map (algebraMap K E) (H i) - C (genericOutputValue H E i) ∈ P := by
  rw [← primeQuotientCoordinate_relations P]
  change aeval (primeQuotientCoordinate P)
    (MvPolynomial.map (algebraMap K E) (H i) - C (genericOutputValue H E i)) = 0
  rw [map_sub, aeval_C, geometric_component_generic_output_evaluation H E P hP i, sub_self]

/-- All original polynomial equations of the map hold at every
point of the entire actual component zero locus. -/
theorem geometric_component_zero_locus_original_output
    (z : Fin 4 → E) (hz : ∀ Q ∈ P, aeval z Q = 0) :
    ∀ i, aeval z (H i) = genericOutputValue H E i := by
  intro i
  have he := hz _ (geometric_component_original_output_relation H E P hP i)
  apply sub_eq_zero.mp
  simpa [aeval_def, MvPolynomial.eval₂_map] using he

omit hP in
/-- Selected independent original outputs stay independent at the
generic output value in every extension of the full output field. -/
theorem generic_output_selected_algebraicIndependent
    (s : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s i.castSucc)))) :
    AlgebraicIndependent K (fun i : Fin 3 => genericOutputValue H E (s i.castSucc)) := by
  let M := polynomialOutputField H
  let y : Fin 3 → M := fun i => fullOutputCoordinate (K := K)
    (fun j => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H j))
    (s i.castSucc)
  have hy : AlgebraicIndependent K y := by
    apply AlgebraicIndependent.of_comp M.val
    exact hY
  exact hy.map' (f := IsScalarTower.toAlgHom K M E) (algebraMap M E).injective

/-- The rank-three generic output cannot be reached by the common
zero locus of an original relatively prime polynomial pair. -/
theorem geometric_component_zero_locus_avoids_coprime_base
    (s : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s i.castSucc))))
    (p q : MvPolynomial (Fin 4) K) (hp : p ≠ 0) (hrel : IsRelPrime p q)
    (z : Fin 4 → E) (hz : ∀ Q ∈ P, aeval z Q = 0) :
    ¬ (aeval z p = 0 ∧ aeval z q = 0) := by
  have hout := geometric_component_zero_locus_original_output H E P hP z hz
  have hind : AlgebraicIndependent K (fun i : Fin 3 => aeval z (H (s i.castSucc))) := by
    simp only [hout]
    exact generic_output_selected_algebraicIndependent H E s hY
  exact three_independent_polynomial_values_avoid_coprime_base z
    (fun i : Fin 3 => H (s i.castSucc)) hind p q hp hrel

end DimensionFourDependence
