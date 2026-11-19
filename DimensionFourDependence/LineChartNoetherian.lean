import DimensionFourDependence.HypersurfaceLineAtlas

/-! # Noetherian line charts and finite irreducible decompositions

The polynomial Zariski topology on a matrix chart is the topology induced
by its evaluation-kernel map into the prime spectrum of the four-variable
polynomial ring. Thus it is Noetherian, as is the actual hypersurface line
chart, and that chart has finitely many irreducible components.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Topology TopologicalSpace

variable {F : Type*} [Field F]

/-- The prime ideal of equations of a matrix-valued rational point of the chart. -/
noncomputable def lineChartEvaluationPrime (B : Matrix (Fin 2) (Fin 2) F) :
    PrimeSpectrum (MvPolynomial (Fin 2 × Fin 2) F) where
  asIdeal := RingHom.ker (aeval (fun ij : Fin 2 × Fin 2 => B ij.1 ij.2) :
    MvPolynomial (Fin 2 × Fin 2) F →ₐ[F] F)
  isPrime := RingHom.ker_isPrime _

/-- Prime-spectrum principal opens pull back to the chart's polynomial principal opens. -/
theorem lineChartEvaluationPrime_preimage_basicOpen (P : MvPolynomial (Fin 2 × Fin 2) F) :
    lineChartEvaluationPrime ⁻¹' (PrimeSpectrum.basicOpen P : Set _) =
      {B | lineChartPolynomialValue B P ≠ 0} := by
  ext B
  exact PrimeSpectrum.mem_basicOpen P (lineChartEvaluationPrime B)

/-- The explicitly generated Zariski topology agrees with the one induced from the spectrum. -/
theorem lineChartEvaluationPrime_isInducing :
    letI := graphLineChartTopology F
    IsInducing (lineChartEvaluationPrime (F := F)) := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) F) := graphLineChartTopology F
  refine ⟨?_⟩
  change graphLineChartTopology F =
    (inferInstance : TopologicalSpace (PrimeSpectrum (MvPolynomial (Fin 2 × Fin 2) F))).induced
      lineChartEvaluationPrime
  rw [PrimeSpectrum.isTopologicalBasis_basic_opens.eq_generateFrom, induced_generateFrom_eq]
  unfold graphLineChartTopology
  apply congrArg TopologicalSpace.generateFrom
  ext U
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨(PrimeSpectrum.basicOpen P : Set _), ⟨P, rfl⟩,
      lineChartEvaluationPrime_preimage_basicOpen P⟩
  · rintro ⟨V, ⟨P, rfl⟩, rfl⟩
    exact ⟨P, lineChartEvaluationPrime_preimage_basicOpen P⟩

/-- The four-parameter line chart is a Noetherian space. -/
theorem graphLineChart_noetherian :
    letI := graphLineChartTopology F
    NoetherianSpace (Matrix (Fin 2) (Fin 2) F) := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) F) := graphLineChartTopology F
  exact lineChartEvaluationPrime_isInducing.noetherianSpace

/-- The actual line chart of any hypersurface is Noetherian. -/
theorem hypersurfaceLineChart_noetherian (R : MvPolynomial (Fin 4) F) :
    letI := graphLineChartTopology F
    NoetherianSpace (hypersurfaceLineChart R) := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) F) := graphLineChartTopology F
  let : NoetherianSpace (Matrix (Fin 2) (Fin 2) F) := graphLineChart_noetherian
  infer_instance

/-- There are finitely many irreducible components of the hypersurface's line chart. -/
theorem hypersurfaceLineChart_finite_irreducibleComponents (R : MvPolynomial (Fin 4) F) :
    letI := graphLineChartTopology F
    (irreducibleComponents (hypersurfaceLineChart R)).Finite := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) F) := graphLineChartTopology F
  let : NoetherianSpace (hypersurfaceLineChart R) := hypersurfaceLineChart_noetherian R
  exact NoetherianSpace.finite_irreducibleComponents

/-- The actual line chart has a finite closed irreducible decomposition. -/
theorem hypersurfaceLineChart_finite_closed_irreducible_cover (R : MvPolynomial (Fin 4) F) :
    letI := graphLineChartTopology F
    ∃ S : Finset (Closeds (hypersurfaceLineChart R)),
      (∀ k : S, IsIrreducible (k : Set (hypersurfaceLineChart R))) ∧
      (⊤ : Closeds (hypersurfaceLineChart R)) = S.sup id := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) F) := graphLineChartTopology F
  let : NoetherianSpace (hypersurfaceLineChart R) := hypersurfaceLineChart_noetherian R
  exact NoetherianSpace.exists_finset_irreducible ⊤

end DimensionFourDependence
