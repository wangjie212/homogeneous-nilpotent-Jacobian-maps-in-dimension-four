import DimensionFourDependence.SegreOriginalFiberInvariants
import DimensionFourDependence.GeometricCoefficientRealization

/-! # The actual Segre fiber equations in the original unpermuted coordinates -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual invariant equations in any specified chart construct a
full polynomial fiber witness, retaining that chart definitionally. -/
noncomputable def fiberEquationWitnessOfInvariants
    (Q : Fin 4 → S₀) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => Q (p i.castSucc)))
    (h c q k : coefficientField (K := K) (fun i : Fin 3 => Q (p i.castSucc)))
    (hh : (h : S₀) = Q (p 3))
    (hc : (c : S₀) = firstFiberInvariantInChart p (fun i : Fin 3 => Q (p i.castSucc)) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (fun i : Fin 3 => Q (p i.castSucc)) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (fun i : Fin 3 => Q (p i.castSucc)) hY h c q) :
    FiberEquationWitness Q := by
  let Y : Fin 3 → S₀ := fun i => Q (p i.castSucc)
  let x : Fin 3 → S₀ := fun i => rationalCoordinate (K := K) (p i.castSucc)
  let P := quadraticFiberEquation Y hY h c q
  let C := cubicFiberEquation Y hY h c q k
  have hA : (fun i => aeval x (pderiv i C)) = fiberThirdCovector p Y hY h c q := by
    funext i
    exact cubicFiberEquation_gradient_aeval p Y hY h c q k i
  have hB : (fun i => aeval x (pderiv i P)) = fiberSecondCovector p Y hY h c := by
    funext i
    exact quadraticFiberEquation_gradient_aeval p Y hY h c q i
  refine {
    chart := p
    independent := hY
    hyperplane := affineFiberEquation Y hY h c
    quadric := P
    cubic := C
    hyperplane_degree := affineFiberEquation_totalDegree Y hY h c
    hyperplane_last_derivative := affineFiberEquation_pderiv_last Y hY h c
    quadric_degree := quadraticFiberEquation_totalDegree Y hY h c q
    cubic_degree := cubicFiberEquation_totalDegree Y hY h c q k
    hyperplane_zero := affineFiberEquation_aeval_zero p Y hY h c hc
    quadric_zero := quadraticFiberEquation_aeval_zero p Y hY h c q hq
    cubic_zero := cubicFiberEquation_aeval_zero p Y hY h c q k hk
    gradients_independent := ?_ }
  intro a b hrel
  apply fiber_covectors_independent Q p hY h c q hh hc hq a b
  change a • (fun i => aeval x (pderiv i C)) + b • (fun i => aeval x (pderiv i P)) = 0 at hrel
  rwa [← hA, ← hB]

/-- The original Segre invariant data construct a complete fiber
witness in the identity chart, with no new source coordinates. -/
noncomputable def segreOriginalFiberEquationWitness
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hind : ¬ComponentsDependent H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (hY : AlgebraicIndependent K (segreOriginalOutputTriple H))
    (c q k : coefficientField (K := K) (segreOriginalOutputTriple H))
    (hc : (c : S₀) = firstFiberInvariantInChart (Equiv.refl (Fin 4))
      (segreOriginalOutputTriple H) hY (segreOriginalCoefficientGraph H))
    (hq : (q : S₀) = secondFiberInvariant (Equiv.refl (Fin 4))
      (segreOriginalOutputTriple H) hY (segreOriginalCoefficientGraph H) c)
    (hk : (k : S₀) = thirdFiberInvariant (Equiv.refl (Fin 4))
      (segreOriginalOutputTriple H) hY (segreOriginalCoefficientGraph H) c q) :
    FiberEquationWitness (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) :=
  fiberEquationWitnessOfInvariants (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))
    (Equiv.refl _) hY (segreOriginalCoefficientGraph H) c q k
    (segre_original_coefficient_graph_value H hind hSegre) hc hq hk

/-- The same specified Segre coefficients are realized on every actual
geometric generic component, retaining the entire original coordinate chart. -/
theorem segre_original_fiber_invariants_geometric_realization
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hind : ¬ComponentsDependent H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (hY : AlgebraicIndependent K (segreOriginalOutputTriple H))
    (c q k : coefficientField (K := K) (segreOriginalOutputTriple H))
    (hc : (c : S₀) = firstFiberInvariantInChart (Equiv.refl (Fin 4))
      (segreOriginalOutputTriple H) hY (segreOriginalCoefficientGraph H))
    (hq : (q : S₀) = secondFiberInvariant (Equiv.refl (Fin 4))
      (segreOriginalOutputTriple H) hY (segreOriginalCoefficientGraph H) c)
    (hk : (k : S₀) = thirdFiberInvariant (Equiv.refl (Fin 4))
      (segreOriginalOutputTriple H) hY (segreOriginalCoefficientGraph H) c q)
    (hrank : polyRank (jac H) = 3)
    (E : Type*) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) :
    Nonempty (FiberCoefficientRealization (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY
      (segreOriginalCoefficientGraph H) c q k (primeQuotientCoordinate P) (genericOutputValue H E)) := by
  let W := segreOriginalFiberEquationWitness H hind hSegre hY c q k hc hq hk
  exact exists_geometric_fiber_coefficient_realization H hrank W (segreOriginalCoefficientGraph H)
    c q k (segre_original_coefficient_graph_value H hind hSegre) hc hq hk E P hP

end DimensionFourDependence
