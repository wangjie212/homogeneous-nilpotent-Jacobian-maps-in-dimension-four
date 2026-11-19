import DimensionFourDependence.ConeFieldExtension

/-! # Degree at most six for all components after algebraic coefficient extension

Each component is represented by the generic coordinates of its prime
quotient. Contraction preserves an original transcendental coordinate;
algebraicity of the coefficient extension keeps it transcendental. The
projective closure therefore has positive degree, bounded by the original
scalar-extended closure's Hilbert function.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {L E F : Type*} [Field L] [Field E] [Field F] [Algebra L E] [Algebra L F]
    [Algebra.IsAlgebraic L E]

/-- Every component after algebraic coefficient extension inherits the
positive degree bound from the original projected fiber closure. -/
theorem component_projective_hilbert_degree_le_six
    (x : Fin 3 → F) (i : Fin 3) (hi : Transcendental L (x i))
    (hupper : ∀ n ≥ 5, projectiveHilbertFunction (projectiveConeIdeal (L := L) x) n ≤ 6 * (n + 1))
    (P : Ideal (MvPolynomial (Fin 3) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal (L := L) x)).minimalPrimes) :
    ∃ d : ℕ, d ≤ 6 ∧ HasCurveHilbertDegree
      (projectiveConeIdeal (L := E) (primeQuotientCoordinate P)) d := by
  let z := primeQuotientCoordinate P
  have hz : Transcendental E (z i) := componentGenericPoint_transcendental x P hP i hi
  have hrel : extendCoefficientIdeal E (fiberVanishingIdeal (L := L) x) ≤
      fiberVanishingIdeal (L := E) z := by
    rw [primeQuotientCoordinate_relations]
    exact hP.le
  have hcone := projectiveConeIdeal_extended_le x z hrel
  apply exists_curve_hilbert_degree_of_linear_bounds _ (projectiveConeIdeal_isHomogeneous z)
  · exact projectiveConeIdeal_hilbert_lower_bound z i hz
  · intro n hn
    calc
      projectiveHilbertFunction (projectiveConeIdeal (L := E) z) n ≤
          projectiveHilbertFunction (extendCoefficientIdeal E (projectiveConeIdeal (L := L) x)) n :=
        projectiveHilbertFunction_antitone hcone n
      _ = projectiveHilbertFunction (projectiveConeIdeal (L := L) x) n :=
        projectiveHilbertFunction_field_extension E _ n
      _ ≤ 6 * (n + 1) := hupper n hn

variable {K : Type*} [Field K] [CharZero K]

/-- Every component of the actual projected fiber after algebraic
extension of the coefficient field has a projective closure of positive
integral Hilbert degree at most six. In particular the extension can be
the algebraic closure of the actual coefficient field. -/
theorem projective_fiber_witness_component_degree
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (W : ProjectiveFiberEquationWitness H) (Fext : Type*) [Field Fext]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc))) Fext]
    [Algebra.IsAlgebraic (coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc))) Fext]
    (P : Ideal (MvPolynomial (Fin 3) Fext)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal Fext (fiberVanishingIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc)))
      (fun i : Fin 3 => rationalCoordinate (K := K) (W.affine.chart i.castSucc)))).minimalPrimes) :
    ∃ d : ℕ, d ≤ 6 ∧ HasCurveHilbertDegree
      (projectiveConeIdeal (L := Fext) (primeQuotientCoordinate P)) d := by
  obtain ⟨i, hi⟩ := exists_transcendental_coordinate
    (L := coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc)))
    (fun i : Fin 3 => rationalCoordinate (K := K) (W.affine.chart i.castSucc))
    (fiber_witness_coordinate_field_eq_top H W.affine.toFiberEquationWitness)
    (by rw [fiber_witness_trdeg_eq_one H hN hrank W.affine.toFiberEquationWitness]; exact one_ne_zero)
  exact component_projective_hilbert_degree_le_six _ i hi
    (projective_fiber_witness_hilbert_le_six H W) P hP

end DimensionFourDependence
