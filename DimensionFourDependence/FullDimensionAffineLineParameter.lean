import DimensionFourDependence.GeometricComponentSourceEvaluation
import DimensionFourDependence.SegreAlgebraicBoundaryConstants

/-! # An actual source line parameter is transcendental over geometric generic constants -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K E G : Type u} [Field K] [Field E] [Field G] [Algebra K E]
    [Algebra E G] [Algebra K G] [IsScalarTower K E G]

/-- Four independent original coordinates on a line over a
three-dimensional constant field have transcendental line parameter. -/
theorem full_dimension_affine_source_line_parameter_transcendental
    (x : Fin 4 → G) (hx : AlgebraicIndependent K x) (a v : Fin 4 → E) (t : G)
    (hpos : ∀ i, x i = algebraMap E G (a i) + algebraMap E G (v i) * t)
    (htr : Algebra.trdeg K E = 3) : Transcendental E t := by
  intro ht
  let C := algebraicClosure E G
  let : IsScalarTower K C G := IsScalarTower.of_algebraMap_eq (by
    intro c
    rw [IsScalarTower.algebraMap_apply K E C, IsScalarTower.algebraMap_apply K E G,
      ← IsScalarTower.algebraMap_apply E C G])
  have halg (i : Fin 4) : IsAlgebraic E (x i) := by
    rw [hpos]
    exact (isAlgebraic_algebraMap (a i)).add ((isAlgebraic_algebraMap (v i)).mul ht)
  let y : Fin 4 → C := fun i => ⟨x i, mem_algebraicClosure_iff.mpr (halg i)⟩
  have hy : AlgebraicIndependent K y := by
    apply AlgebraicIndependent.of_comp (IsScalarTower.toAlgHom K C G)
    exact hx
  have hC : Algebra.trdeg K C = 3 := by
    have he := trdeg_add_eq (A := C) K E
    simpa only [trdeg_eq_zero, htr, add_zero] using he.symm
  have hge : 4 ≤ Algebra.trdeg K C := by simpa using hy.lift_cardinalMk_le_trdeg
  rw [hC] at hge
  norm_num at hge

variable [CharZero K]

/-- The original component constructs transcendence of every specified
affine-line parameter over its actual algebraic generic constants. -/
theorem original_geometric_generic_component_affine_line_parameter_transcendental
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (a v : Fin 4 → E) (t : FractionRing (MvPolynomial (Fin 4) E ⧸ P))
    (hpos : ∀ i, primeQuotientCoordinate P i = algebraMap E _ (a i) + algebraMap E _ (v i) * t) :
    Transcendental E t :=
  full_dimension_affine_source_line_parameter_transcendental (primeQuotientCoordinate P)
    (geometric_component_original_source_coordinates_algebraicIndependent H E P hP) a v t hpos
    (rank_three_output_algebraic_extension_absolute_trdeg H hrank)

end DimensionFourDependence
