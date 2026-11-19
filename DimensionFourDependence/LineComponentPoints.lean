import DimensionFourDependence.LineChartNoetherian
import DimensionFourDependence.LineChartBaseChange
import Mathlib.RingTheory.Nullstellensatz

/-! # Actual rational points of an original-field line component

Over algebraically closed coefficients, the matrix points cut out by a
prime component ideal have exactly that vanishing ideal. Their evaluation
primes have that same spectrum vanishing ideal, so these actual matrix
points form a nonempty irreducible family in the checked chart topology.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Topology

variable {K : Type*} [Field K]

/-- Actual matrices satisfying every original-field equation of a line component. -/
def lineComponentPoints (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K)) :
    Set (Matrix (Fin 2) (Fin 2) K) :=
  {B | ∀ P ∈ Q, lineChartPolynomialValue B P = 0}

/-- The actual points of a line component form a closed matrix-chart subfamily. -/
theorem lineComponentPoints_isClosed (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K)) :
    @IsClosed _ (graphLineChartTopology K) (lineComponentPoints Q) :=
  lineChart_equations_isClosed (Q : Set (MvPolynomial (Fin 2 × Fin 2) K))

/-- Every actual point of a chart component represents a contained hypersurface line. -/
theorem lineComponentPoints_le_hypersurfaceLineChart
    (R : MvPolynomial (Fin 4) K) (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K))
    (hQ : graphLineEquationIdeal R ≤ Q) : lineComponentPoints Q ⊆ hypersurfaceLineChart R := by
  intro B hB
  apply (graphLine_equations_iff_restriction_zero B R).mp
  intro P hP
  exact hB P (hQ (Ideal.subset_span hP))

variable [IsAlgClosed K]
variable (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K)) [Q.IsPrime]

/-- A polynomial vanishes on all actual matrices of a prime component
exactly when it belongs to that original component ideal. -/
theorem lineComponentPoints_polynomial_vanishes_iff (P : MvPolynomial (Fin 2 × Fin 2) K) :
    (∀ B ∈ lineComponentPoints Q, lineChartPolynomialValue B P = 0) ↔ P ∈ Q := by
  constructor
  · intro h
    have hp : P ∈ MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K Q) := by
      intro x hx
      exact h (fun i j => x (i, j)) (fun R hR => hx R hR)
    rwa [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hp
  · intro h B hB
    exact hB P h

/-- The evaluation-prime image of the actual matrices has precisely the
original prime component as its spectrum vanishing ideal. -/
theorem lineComponentPoints_spectrum_vanishingIdeal :
    PrimeSpectrum.vanishingIdeal (lineChartEvaluationPrime '' lineComponentPoints Q) = Q := by
  ext P
  rw [PrimeSpectrum.mem_vanishingIdeal]
  constructor
  · intro h
    apply (lineComponentPoints_polynomial_vanishes_iff Q P).mp
    intro B hB
    exact h _ ⟨B, hB, rfl⟩
  · intro h x hx
    obtain ⟨B, hB, rfl⟩ := hx
    exact hB P h

/-- Actual matrix points of a prime line component over algebraically
closed coefficients are nonempty and irreducible in the actual chart topology. -/
theorem lineComponentPoints_isIrreducible :
    letI := graphLineChartTopology K
    IsIrreducible (lineComponentPoints Q) := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) K) := graphLineChartTopology K
  have himage : IsIrreducible (lineChartEvaluationPrime '' lineComponentPoints Q) := by
    apply PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mpr
    rw [lineComponentPoints_spectrum_vanishingIdeal Q]
    infer_instance
  refine ⟨?_, ?_⟩
  · obtain ⟨_, B, hB, rfl⟩ := himage.nonempty
    exact ⟨B, hB⟩
  · intro U V hU hV hUne hVne
    obtain ⟨U', hU', rfl⟩ := lineChartEvaluationPrime_isInducing.isOpen_iff.mp hU
    obtain ⟨V', hV', rfl⟩ := lineChartEvaluationPrime_isInducing.isOpen_iff.mp hV
    obtain ⟨B, hB, hBU⟩ := hUne
    obtain ⟨D, hD, hDV⟩ := hVne
    obtain ⟨_, ⟨T, hT, rfl⟩, hTU, hTV⟩ := himage.isPreirreducible U' V' hU' hV'
      ⟨_, ⟨B, hB, rfl⟩, hBU⟩ ⟨_, ⟨D, hD, rfl⟩, hDV⟩
    exact ⟨T, hT, hTU, hTV⟩

end DimensionFourDependence
