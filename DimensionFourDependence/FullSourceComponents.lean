import DimensionFourDependence.FullOutputFiber

/-! # Component degree bounds in the original source space -/

namespace DimensionFourDependence

open MvPolynomial

variable {L E F : Type*} [Field L] [Field E] [Field F] [Algebra L E] [Algebra L F]
    [Algebra.IsAlgebraic L E] {n : ℕ}

/-- The linear Hilbert bound passes to every component in any affine dimension. -/
theorem component_hilbert_degree_le_six
    (x : Fin n → F) (i : Fin n) (hi : Transcendental L (x i))
    (hupper : ∀ d ≥ 5, projectiveHilbertFunction (projectiveConeIdeal (L := L) x) d ≤ 6 * (d + 1))
    (P : Ideal (MvPolynomial (Fin n) E)) [P.IsPrime]
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
  · intro d hd
    calc
      projectiveHilbertFunction (projectiveConeIdeal (L := E) z) d ≤
          projectiveHilbertFunction (extendCoefficientIdeal E (projectiveConeIdeal (L := L) x)) d :=
        projectiveHilbertFunction_antitone hcone d
      _ = projectiveHilbertFunction (projectiveConeIdeal (L := L) x) d :=
        projectiveHilbertFunction_field_extension E _ d
      _ ≤ 6 * (d + 1) := hupper d hd

variable {K : Type*} [Field K] [CharZero K]

/-- Every component after algebraic extension of the actual coefficient
field has degree between one and six in the original projective four-space. -/
theorem full_source_fiber_witness_component_degree
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (W : ProjectiveFiberEquationWitness H) (Fext : Type*) [Field Fext]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc))) Fext]
    [Algebra.IsAlgebraic (coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc))) Fext]
    (P : Ideal (MvPolynomial (Fin 4) Fext)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal Fext (fiberVanishingIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc)))
      (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) :
    ∃ d : ℕ, d ≤ 6 ∧ HasCurveHilbertDegree
      (projectiveConeIdeal (L := Fext) (primeQuotientCoordinate P)) d := by
  obtain ⟨i, hi⟩ := exists_transcendental_coordinate
    (L := coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc)))
    (fun i : Fin 3 => rationalCoordinate (K := K) (W.affine.chart i.castSucc))
    (fiber_witness_coordinate_field_eq_top H W.affine.toFiberEquationWitness)
    (by rw [fiber_witness_trdeg_eq_one H hN hrank W.affine.toFiberEquationWitness]; exact one_ne_zero)
  apply component_hilbert_degree_le_six (rationalCoordinate (K := K) (n := 4))
    (W.affine.chart i.castSucc) hi _ P hP
  intro d hd
  rw [fiber_witness_full_source_hilbert H W.affine.toFiberEquationWitness]
  exact projective_fiber_witness_hilbert_le_six H W d hd

end DimensionFourDependence
