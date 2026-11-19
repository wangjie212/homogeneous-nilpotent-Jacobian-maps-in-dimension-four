import DimensionFourDependence.LineComponentPoints

/-! # Polynomial coordinates for pairs of actual line parameters

The two matrix charts give eight independent parameter coordinates.
Specializing either matrix leaves a polynomial in the other. The pair
of original component ideals cuts out exactly the actual product of
their matrix points over the coefficient field.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

abbrev LineMatrixIndex := Fin 2 × Fin 2
abbrev LinePairIndex := LineMatrixIndex ⊕ LineMatrixIndex

variable {K : Type*} [Field K]

/-- The actual eight coordinates of a pair of matrix-chart parameters. -/
def linePairCoordinates (B D : Matrix (Fin 2) (Fin 2) K) : LinePairIndex → K :=
  Sum.elim (fun ij => B ij.1 ij.2) (fun ij => D ij.1 ij.2)

/-- Fix the second matrix, leaving the first matrix as polynomial variables. -/
noncomputable def linePairSpecializeRight (D : Matrix (Fin 2) (Fin 2) K)
    (P : MvPolynomial LinePairIndex K) : MvPolynomial LineMatrixIndex K :=
  aeval (Sum.elim (fun ij => X ij) (fun ij => MvPolynomial.C (D ij.1 ij.2))) P

/-- Fix the first matrix, leaving the second matrix as polynomial variables. -/
noncomputable def linePairSpecializeLeft (B : Matrix (Fin 2) (Fin 2) K)
    (P : MvPolynomial LinePairIndex K) : MvPolynomial LineMatrixIndex K :=
  aeval (Sum.elim (fun ij => MvPolynomial.C (B ij.1 ij.2)) (fun ij => X ij)) P

/-- Specializing the second matrix then evaluating the first is actual pair evaluation. -/
theorem linePairSpecializeRight_eval (B D : Matrix (Fin 2) (Fin 2) K)
    (P : MvPolynomial LinePairIndex K) :
    lineChartPolynomialValue B (linePairSpecializeRight D P) = aeval (linePairCoordinates B D) P := by
  unfold lineChartPolynomialValue linePairSpecializeRight
  rw [comp_aeval_apply]
  apply congrArg (fun z : LinePairIndex → K => aeval z P)
  funext ij
  cases ij <;> simp [linePairCoordinates]

/-- Specializing the first matrix then evaluating the second is actual pair evaluation. -/
theorem linePairSpecializeLeft_eval (B D : Matrix (Fin 2) (Fin 2) K)
    (P : MvPolynomial LinePairIndex K) :
    lineChartPolynomialValue D (linePairSpecializeLeft B P) = aeval (linePairCoordinates B D) P := by
  unfold lineChartPolynomialValue linePairSpecializeLeft
  rw [comp_aeval_apply]
  apply congrArg (fun z : LinePairIndex → K => aeval z P)
  funext ij
  cases ij <;> simp [linePairCoordinates]

/-- Vanishing against every member of a fixed right subfamily is a
closed condition in the actual left matrix chart. -/
theorem linePair_polynomial_all_right_isClosed
    (T : Set (Matrix (Fin 2) (Fin 2) K)) (P : MvPolynomial LinePairIndex K) :
    @IsClosed _ (graphLineChartTopology K)
      {B | ∀ D ∈ T, aeval (linePairCoordinates B D) P = 0} := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) K) := graphLineChartTopology K
  simp only [← linePairSpecializeRight_eval, Set.ofPred_forall]
  exact isClosed_iInter (fun D => isClosed_iInter (fun _ =>
    lineChart_polynomial_zero_isClosed (linePairSpecializeRight D P)))

/-- Actual coordinate points of the product of two original component families. -/
def lineComponentPairPoints (Q Q' : Ideal (MvPolynomial LineMatrixIndex K)) :
    Set (LinePairIndex → K) :=
  {z | ∃ B ∈ lineComponentPoints Q, ∃ D ∈ lineComponentPoints Q', z = linePairCoordinates B D}

/-- The actual ideal of equations on all pairs of component matrices. -/
noncomputable def lineComponentPairIdeal (Q Q' : Ideal (MvPolynomial LineMatrixIndex K)) :
    Ideal (MvPolynomial LinePairIndex K) :=
  MvPolynomial.vanishingIdeal K (lineComponentPairPoints Q Q')

/-- Membership means identical vanishing on every actual matrix pair. -/
theorem mem_lineComponentPairIdeal_iff
    (Q Q' : Ideal (MvPolynomial LineMatrixIndex K)) (P : MvPolynomial LinePairIndex K) :
    P ∈ lineComponentPairIdeal Q Q' ↔
      ∀ B ∈ lineComponentPoints Q, ∀ D ∈ lineComponentPoints Q',
        aeval (linePairCoordinates B D) P = 0 := by
  constructor
  · intro h B hB D hD
    exact h _ ⟨B, hB, D, hD, rfl⟩
  · intro h z hz
    obtain ⟨B, hB, D, hD, rfl⟩ := hz
    exact h B hB D hD

/-- The sum of the original equations in the separate left and right coordinates. -/
noncomputable def linePairCoefficientIdeal (Q Q' : Ideal (MvPolynomial LineMatrixIndex K)) :
    Ideal (MvPolynomial LinePairIndex K) :=
  Q.map (MvPolynomial.rename Sum.inl) ⊔ Q'.map (MvPolynomial.rename Sum.inr)

variable {E : Type*} [Field E] [Algebra K E]

/-- A pair over any extension field satisfies the pair coefficient
ideal exactly when each matrix satisfies its own original component ideal. -/
theorem linePairCoefficientIdeal_le_evalKernel_iff
    (Q Q' : Ideal (MvPolynomial LineMatrixIndex K)) (B D : Matrix (Fin 2) (Fin 2) E) :
    linePairCoefficientIdeal Q Q' ≤
      RingHom.ker (aeval (linePairCoordinates B D) : MvPolynomial LinePairIndex K →ₐ[K] E) ↔
      Q ≤ (extendedLineChartPrime (K := K) B).asIdeal ∧
      Q' ≤ (extendedLineChartPrime (K := K) D).asIdeal := by
  have hleft : (RingHom.ker (aeval (linePairCoordinates B D) : MvPolynomial LinePairIndex K →ₐ[K] E)).comap
      (MvPolynomial.rename Sum.inl) = (extendedLineChartPrime (K := K) B).asIdeal := by
    ext P
    change aeval (linePairCoordinates B D) (rename Sum.inl P) = 0 ↔
      extendedLineChartSpecialization B P = 0
    rw [aeval_rename]
    rfl
  have hright : (RingHom.ker (aeval (linePairCoordinates B D) : MvPolynomial LinePairIndex K →ₐ[K] E)).comap
      (MvPolynomial.rename Sum.inr) = (extendedLineChartPrime (K := K) D).asIdeal := by
    ext P
    change aeval (linePairCoordinates B D) (rename Sum.inr P) = 0 ↔
      extendedLineChartSpecialization D P = 0
    rw [aeval_rename]
    rfl
  rw [linePairCoefficientIdeal, sup_le_iff, Ideal.map_le_iff_le_comap,
    Ideal.map_le_iff_le_comap, hleft, hright]

/-- The pair coefficient equations cut out exactly the actual product
of the two component families over the coefficient field. -/
theorem linePairCoefficientIdeal_zeroLocus
    (Q Q' : Ideal (MvPolynomial LineMatrixIndex K)) :
    MvPolynomial.zeroLocus K (linePairCoefficientIdeal Q Q') = lineComponentPairPoints Q Q' := by
  ext z
  let B : Matrix (Fin 2) (Fin 2) K := fun i j => z (Sum.inl (i, j))
  let D : Matrix (Fin 2) (Fin 2) K := fun i j => z (Sum.inr (i, j))
  have hz : z = linePairCoordinates B D := by
    funext ij
    cases ij <;> rfl
  rw [hz]
  constructor
  · intro h
    have he := (linePairCoefficientIdeal_le_evalKernel_iff Q Q' B D).mp h
    exact ⟨B, he.1, D, he.2, rfl⟩
  · rintro ⟨B', hB', D', hD', he⟩
    rw [he]
    exact (linePairCoefficientIdeal_le_evalKernel_iff Q Q' B' D').mpr ⟨hB', hD'⟩

end DimensionFourDependence
