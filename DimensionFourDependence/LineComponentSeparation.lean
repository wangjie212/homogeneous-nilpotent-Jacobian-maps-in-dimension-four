import DimensionFourDependence.LineComponentPoints
import DimensionFourDependence.UniversalLineIncidence
import DimensionFourDependence.FiniteLineChartFibers

/-! # Actual component points separate the universal line family

The Nullstellensatz separates elements of the quotient parameter ring.
Polynomial evaluation in the two free line coordinates then separates
the entire universal incidence ring. Consequently an original polynomial
vanishing on every actual member line lies in the actual incidence kernel.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K]

/-- An actual point satisfying all component equations gives the
evaluation prime needed by the quotient specialization. -/
theorem lineComponentPoints_le_extendedPrime
    (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K))
    (B : Matrix (Fin 2) (Fin 2) K) (hB : B ∈ lineComponentPoints Q) :
    Q ≤ (extendedLineChartPrime (K := K) B).asIdeal := hB

variable [IsAlgClosed K]
variable (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K)) [Q.IsPrime]

/-- Actual matrix points of a component separate every element of its
original-field quotient parameter ring. -/
theorem componentLineParameter_separated_by_points
    (a : MvPolynomial (Fin 2 × Fin 2) K ⧸ Q)
    (ha : ∀ B (hB : B ∈ lineComponentPoints Q),
      componentLineParameterEvaluation B Q (lineComponentPoints_le_extendedPrime Q B hB) a = 0) :
    a = 0 := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (lineComponentPoints_polynomial_vanishes_iff Q P).mp
  intro B hB
  exact ha B hB

/-- Evaluation at all actual matrix points and all actual line coordinates
separates the entire universal incidence polynomial ring. -/
theorem componentLineIncidence_separated_by_points
    (P : MvPolynomial (Fin 2) (MvPolynomial (Fin 2 × Fin 2) K ⧸ Q))
    (hP : ∀ B (hB : B ∈ lineComponentPoints Q) (u : Fin 2 → K),
      componentLineIncidenceEvaluation B u Q (lineComponentPoints_le_extendedPrime Q B hB) P = 0) :
    P = 0 := by
  have hm (B : Matrix (Fin 2) (Fin 2) K) (hB : B ∈ lineComponentPoints Q) :
      MvPolynomial.map
        (componentLineParameterEvaluation B Q
          (lineComponentPoints_le_extendedPrime Q B hB)).toRingHom P = 0 := by
    apply MvPolynomial.funext
    intro u
    change componentLineIncidenceEvaluation B u Q
      (lineComponentPoints_le_extendedPrime Q B hB) P = 0
    exact hP B hB u
  apply MvPolynomial.ext
  intro m
  apply componentLineParameter_separated_by_points Q (P.coeff m)
  intro B hB
  have he := congrArg (fun S : MvPolynomial (Fin 2) K => S.coeff m) (hm B hB)
  rw [coeff_map] at he
  exact he

/-- An original polynomial vanishing on all actual member lines of a
component vanishes in its universal incidence ring. -/
theorem componentLineIncidenceHom_eq_zero_of_component_lines
    (p : Equiv.Perm (Fin 4)) (P : MvPolynomial (Fin 4) K)
    (hP : ∀ B ∈ lineComponentPoints Q, ∀ x ∈ lineChartMemberLine p B, aeval x P = 0) :
    componentLineIncidenceHom p Q P = 0 := by
  apply componentLineIncidence_separated_by_points Q
  intro B hB u
  rw [componentLineIncidenceHom_evaluate]
  apply hP B hB
  exact ⟨![u 0, u 1, (B *ᵥ u) 0, (B *ᵥ u) 1],
    (mem_graphLineFour B _).mpr ⟨u, rfl⟩, rfl⟩

end DimensionFourDependence
