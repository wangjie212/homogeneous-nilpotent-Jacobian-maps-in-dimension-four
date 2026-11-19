import DimensionFourDependence.LinePairParameters

/-! # The actual product of two line components is irreducible

The ideal of all actual matrix pairs is prime. One specializes a product
of polynomials at the first matrix, uses the prime second component,
and then uses irreducibility of the first component for the two closed
uniform-vanishing conditions. The Nullstellensatz identifies this prime
with the radical of the separate original component equations, so all
extension-field pairs satisfy it as well.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Topology

variable {K : Type*} [Field K] [IsAlgClosed K]
variable (Q Q' : Ideal (MvPolynomial LineMatrixIndex K)) [Q.IsPrime] [Q'.IsPrime]

/-- The ideal of equations of all actual pairs of component matrices is prime. -/
@[instance]
theorem lineComponentPairIdeal_isPrime : (lineComponentPairIdeal Q Q').IsPrime := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) K) := graphLineChartTopology K
  apply Ideal.isPrime_iff.mpr
  refine ⟨?_, ?_⟩
  · intro htop
    obtain ⟨B, hB⟩ := (lineComponentPoints_isIrreducible Q).nonempty
    obtain ⟨D, hD⟩ := (lineComponentPoints_isIrreducible Q').nonempty
    have h1 : (1 : MvPolynomial LinePairIndex K) ∈ lineComponentPairIdeal Q Q' := by
      rw [htop]
      trivial
    have hz := (mem_lineComponentPairIdeal_iff Q Q' 1).mp h1 B hB D hD
    exact one_ne_zero (by simpa only [map_one] using hz)
  · intro P R hPR
    have hpoint (B) (hB : B ∈ lineComponentPoints Q) (D) (hD : D ∈ lineComponentPoints Q') :
        aeval (linePairCoordinates B D) P * aeval (linePairCoordinates B D) R = 0 := by
      exact (map_mul (aeval (linePairCoordinates B D)) P R).symm.trans
        ((mem_lineComponentPairIdeal_iff Q Q' (P * R)).mp hPR B hB D hD)
    have hsplit (B) (hB : B ∈ lineComponentPoints Q) :
        (∀ D ∈ lineComponentPoints Q', aeval (linePairCoordinates B D) P = 0) ∨
        (∀ D ∈ lineComponentPoints Q', aeval (linePairCoordinates B D) R = 0) := by
      have hprod : linePairSpecializeLeft B P * linePairSpecializeLeft B R ∈ Q' := by
        apply (lineComponentPoints_polynomial_vanishes_iff Q' _).mp
        intro D hD
        change (aeval (fun ij => D ij.1 ij.2))
          (linePairSpecializeLeft B P * linePairSpecializeLeft B R) = 0
        rw [map_mul]
        change lineChartPolynomialValue D (linePairSpecializeLeft B P) *
          lineChartPolynomialValue D (linePairSpecializeLeft B R) = 0
        rw [linePairSpecializeLeft_eval, linePairSpecializeLeft_eval]
        exact hpoint B hB D hD
      rcases (inferInstance : Q'.IsPrime).mem_or_mem hprod with hP | hR
      · exact Or.inl (fun D hD => (linePairSpecializeLeft_eval B D P).symm.trans (hD _ hP))
      · exact Or.inr (fun D hD => (linePairSpecializeLeft_eval B D R).symm.trans (hD _ hR))
    let CP : Set (Matrix (Fin 2) (Fin 2) K) :=
      {B | ∀ D ∈ lineComponentPoints Q', aeval (linePairCoordinates B D) P = 0}
    let CR : Set (Matrix (Fin 2) (Fin 2) K) :=
      {B | ∀ D ∈ lineComponentPoints Q', aeval (linePairCoordinates B D) R = 0}
    have hcover : lineComponentPoints Q ⊆ CP ∪ CR := fun B hB => hsplit B hB
    rcases isPreirreducible_iff_isClosed_union_isClosed.mp
      (lineComponentPoints_isIrreducible Q).isPreirreducible CP CR
      (linePair_polynomial_all_right_isClosed _ P)
      (linePair_polynomial_all_right_isClosed _ R) hcover with hP | hR
    · exact Or.inl ((mem_lineComponentPairIdeal_iff Q Q' P).mpr hP)
    · exact Or.inr ((mem_lineComponentPairIdeal_iff Q Q' R).mpr hR)

omit [Q.IsPrime] [Q'.IsPrime] in
/-- The actual product ideal is exactly the radical of the original
left and right component equations in the separate pair coordinates. -/
theorem lineComponentPairIdeal_eq_radical :
    lineComponentPairIdeal Q Q' = (linePairCoefficientIdeal Q Q').radical := by
  unfold lineComponentPairIdeal
  rw [← linePairCoefficientIdeal_zeroLocus]
  exact MvPolynomial.vanishingIdeal_zeroLocus_eq_radical _

/-- The actual product has exactly the original left component relations. -/
theorem lineComponentPairIdeal_comap_left :
    (lineComponentPairIdeal Q Q').comap (MvPolynomial.rename Sum.inl) = Q := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) K) := graphLineChartTopology K
  ext P
  change rename Sum.inl P ∈ lineComponentPairIdeal Q Q' ↔ P ∈ Q
  rw [mem_lineComponentPairIdeal_iff]
  constructor
  · intro h
    apply (lineComponentPoints_polynomial_vanishes_iff Q P).mp
    intro B hB
    obtain ⟨D, hD⟩ := (lineComponentPoints_isIrreducible Q').nonempty
    have he := h B hB D hD
    rw [aeval_rename] at he
    exact he
  · intro h B hB D _
    rw [aeval_rename]
    exact hB P h

/-- The actual product has exactly the original right component relations. -/
theorem lineComponentPairIdeal_comap_right :
    (lineComponentPairIdeal Q Q').comap (MvPolynomial.rename Sum.inr) = Q' := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) K) := graphLineChartTopology K
  ext P
  change rename Sum.inr P ∈ lineComponentPairIdeal Q Q' ↔ P ∈ Q'
  rw [mem_lineComponentPairIdeal_iff]
  constructor
  · intro h
    apply (lineComponentPoints_polynomial_vanishes_iff Q' P).mp
    intro D hD
    obtain ⟨B, hB⟩ := (lineComponentPoints_isIrreducible Q).nonempty
    have he := h B hB D hD
    rw [aeval_rename] at he
    exact he
  · intro h B _ D hD
    rw [aeval_rename]
    exact hD P h

variable {E : Type*} [Field E] [Algebra K E]

omit [Q.IsPrime] [Q'.IsPrime] in
/-- Every pair of extension-field component points satisfies every
actual original-field product relation. -/
theorem lineComponentPairIdeal_le_extension_evalKernel
    (B D : Matrix (Fin 2) (Fin 2) E)
    (hB : Q ≤ (extendedLineChartPrime (K := K) B).asIdeal)
    (hD : Q' ≤ (extendedLineChartPrime (K := K) D).asIdeal) :
    lineComponentPairIdeal Q Q' ≤
      RingHom.ker (aeval (linePairCoordinates B D) : MvPolynomial LinePairIndex K →ₐ[K] E) := by
  rw [lineComponentPairIdeal_eq_radical]
  apply (RingHom.ker_isPrime (aeval (linePairCoordinates B D) :
    MvPolynomial LinePairIndex K →ₐ[K] E)).isRadical.radical_le_iff.mpr
  exact (linePairCoefficientIdeal_le_evalKernel_iff Q Q' B D).mpr ⟨hB, hD⟩

end DimensionFourDependence
