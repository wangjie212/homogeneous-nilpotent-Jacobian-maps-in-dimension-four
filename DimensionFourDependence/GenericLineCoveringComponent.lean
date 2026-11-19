import DimensionFourDependence.UniversalLineIncidence
import DimensionFourDependence.GenericOutputPoint
import DimensionFourDependence.ImageHypersurface

/-! # A line through the actual generic image gives a covering chart component

An original-field component of the line parameter chart supports a
universal incidence map. Specialization to the actual generic image point
proves that this map has exactly the original image ideal as its kernel.
Consequently its spectrum image has closure equal to the actual affine
image cone. This constructs covering components; their dimensions and
the incidence between two covering families are still separate obligations.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Topology

variable {K : Type*} [Field K]

/-- A minimal-prime component of a line chart is an irreducible parameter spectrum. -/
theorem line_chart_component_parameter_spectrum_irreducible
    (R : MvPolynomial (Fin 4) K) (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K))
    (hQ : Q ∈ (graphLineEquationIdeal R).minimalPrimes) :
    IrreducibleSpace (PrimeSpectrum (MvPolynomial (Fin 2 × Fin 2) K ⧸ Q)) := by
  let : Q.IsPrime := hQ.isPrime
  infer_instance

/-- The universal incidence over a minimal-prime chart component is irreducible. -/
theorem line_chart_component_incidence_spectrum_irreducible
    (R : MvPolynomial (Fin 4) K) (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K))
    (hQ : Q ∈ (graphLineEquationIdeal R).minimalPrimes) :
    IrreducibleSpace (PrimeSpectrum (MvPolynomial (Fin 2) (MvPolynomial (Fin 2 × Fin 2) K ⧸ Q))) := by
  let : Q.IsPrime := hQ.isPrime
  infer_instance

variable {E : Type*} [CharZero K] [Field E] [Algebra K E]

/-- A chart component containing a line through the actual generic image
has precisely the actual image relations as its universal-incidence kernel. -/
theorem generic_line_component_incidence_kernel_eq_imageIdeal
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E]
    (s : hypersurfaceLineAtlas (MvPolynomial.map (algebraMap K E) I.equation))
    (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K))
    (hequations : graphLineEquationIdeal (rename s.1.symm I.equation) ≤ Q)
    (hparameter : Q ≤ (extendedLineChartPrime (K := K) s.2.val).asIdeal)
    (hpoint : genericOutputValue H E ∈ hypersurfaceAtlasLine _ s) :
    RingHom.ker (componentLineIncidenceHom s.1 Q) = imageRelationIdeal H := by
  obtain ⟨u, hu⟩ := hypersurfaceAtlasLine_point_coordinates _ s (genericOutputValue H E) hpoint
  apply le_antisymm
  · intro F hF
    change componentLineIncidenceHom s.1 Q F = 0 at hF
    have he := componentLineIncidenceHom_evaluate s.1 s.2.val u Q hparameter F
    rw [hF, map_zero, ← hu] at he
    exact (genericOutputValue_relations H E F).mp he.symm
  · rw [I.ideal_eq_span H hrank]
    apply Ideal.span_le.mpr
    intro F hF
    obtain rfl := Set.mem_singleton_iff.mp hF
    exact componentLineIncidenceHom_equation_zero I.equation s.1 Q hequations

/-- The universal incidence over that component covers the actual affine
image cone in the precise sense of dense spectrum image. -/
theorem generic_line_component_incidence_image_closure
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E]
    (s : hypersurfaceLineAtlas (MvPolynomial.map (algebraMap K E) I.equation))
    (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K))
    (hequations : graphLineEquationIdeal (rename s.1.symm I.equation) ≤ Q)
    (hparameter : Q ≤ (extendedLineChartPrime (K := K) s.2.val).asIdeal)
    (hpoint : genericOutputValue H E ∈ hypersurfaceAtlasLine _ s) :
    closure (Set.range (PrimeSpectrum.comap (componentLineIncidenceHom s.1 Q).toRingHom)) =
      PrimeSpectrum.zeroLocus (imageRelationIdeal H : Set (MvPolynomial (Fin 4) K)) := by
  rw [PrimeSpectrum.closure_range_comap]
  exact congrArg (fun J : Ideal (MvPolynomial (Fin 4) K) =>
    PrimeSpectrum.zeroLocus (J : Set (MvPolynomial (Fin 4) K)))
    (generic_line_component_incidence_kernel_eq_imageIdeal H hrank I s Q hequations hparameter hpoint)

/-- Every actual generic image line supplies an original-field minimal-prime
line-chart component whose universal family has dense image in the actual image cone. -/
theorem generic_image_line_exists_covering_chart_component
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E]
    (s : hypersurfaceLineAtlas (MvPolynomial.map (algebraMap K E) I.equation))
    (hpoint : genericOutputValue H E ∈ hypersurfaceAtlasLine _ s) :
    ∃ Q ∈ (graphLineEquationIdeal (rename s.1.symm I.equation)).minimalPrimes,
      Q ≤ (extendedLineChartPrime (K := K) s.2.val).asIdeal ∧
      RingHom.ker (componentLineIncidenceHom s.1 Q) = imageRelationIdeal H ∧
      closure (Set.range (PrimeSpectrum.comap (componentLineIncidenceHom s.1 Q).toRingHom)) =
        PrimeSpectrum.zeroLocus (imageRelationIdeal H : Set (MvPolynomial (Fin 4) K)) := by
  obtain ⟨Q, hminimal, hparameter⟩ := atlas_point_exists_original_field_component I.equation s
  exact ⟨Q, hminimal, hparameter,
    generic_line_component_incidence_kernel_eq_imageIdeal H hrank I s Q hminimal.le hparameter hpoint,
    generic_line_component_incidence_image_closure H hrank I s Q hminimal.le hparameter hpoint⟩

end DimensionFourDependence
