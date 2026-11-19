import DimensionFourDependence.SegreGeometricBoundaryAlgebraicity
import DimensionFourDependence.SegreProjectiveRulingPoints
import DimensionFourDependence.ProjectiveNormalizedPrimeCoordinates

/-! # Finite original ruling fields for actual projective boundary primes -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [Field E] [Algebra K E]

/-- The specified original ruling parameter inside the actual normalized
coordinate field of an original projective prime. -/
noncomputable def segreProjectiveRulingParameterField
    (K : Type u) [Field K] [Algebra K E] (Y : Fin 4 → E) (j : Fin 3)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E)) (a : Fin 4) :
    IntermediateField K (projectivePrimeRatioField p (some a)) :=
  IntermediateField.adjoin K
    ({algebraMap E (projectivePrimeRatioField p (some a)) (Y j.castSucc / Y 0)} : Set _)

/-- An actual projective point has its original normalized four-coordinate
representative over one finite extension of its specified original ruling
parameter. The finite field is a subfield of the actual coordinate field. -/
def SegreFiniteRulingBoundaryPoint
    (K : Type u) [Field K] [Algebra K E] (Y : Fin 4 → E) (j : Fin 3)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E)) : Prop :=
  ∃ a : Fin 4, X (some a) ∉ p.asHomogeneousIdeal ∧
    ∃ B : IntermediateField (segreProjectiveRulingParameterField K Y j p a)
        (projectivePrimeRatioField p (some a)),
      Module.Finite (segreProjectiveRulingParameterField K Y j p a) B ∧
        ∀ i : Fin 4, projectivePrimeRatioCoordinate p (some a) (some i) ∈ B

variable [CharZero K]

/-- Every prime of the actual geometric infinity section on either
original Segre ruling has a finite branch over its original parameter.
The proof constructs its normalized representative and proves algebraicity
using the original nilpotent map and Lemma 5.2. -/
theorem geometric_segre_ruling_boundary_point_has_finite_parameter_branch
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [IsScalarTower K (polynomialOutputField H) E]
    (Q : Ideal (MvPolynomial (Fin 4) E)) [Q.IsPrime]
    (hQ : Q ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (j : Fin 3) (hj : j ≠ 0)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hboundary : p ∈ projectiveClosureSet (L := E) (primeQuotientCoordinate Q))
    (hinfty : X none ∈ p.asHomogeneousIdeal)
    (hR0 : segreRulingLinearPolynomial (genericOutputValue H E j.castSucc / genericOutputValue H E 0)
      j.castSucc 0 ∈ p.asHomogeneousIdeal)
    (hR1 : segreRulingLinearPolynomial (genericOutputValue H E j.castSucc / genericOutputValue H E 0)
      3 (if j = 1 then 2 else 1) ∈ p.asHomogeneousIdeal) :
    SegreFiniteRulingBoundaryPoint K (genericOutputValue H E) j p := by
  obtain ⟨a, ha⟩ : ∃ a : Fin 4, X (some a) ∉ p.asHomogeneousIdeal := by
    obtain ⟨a, ha⟩ := projectiveSpectrum_exists_coordinate_not_mem p
    cases a with
    | none => exact False.elim (ha hinfty)
    | some a => exact ⟨a, ha⟩
  let κ := projectivePrimeRatioField p (some a)
  let z := projectivePrimeRatioCoordinate p (some a)
  have hz : z ≠ 0 := projectivePrimeRatioCoordinate_ne_zero p (some a) ha
  have hnorm : z (some a) = 1 := projectivePrimeRatioCoordinate_self p (some a) ha
  have hrep : projectiveFieldPoint (E := E) z hz = p :=
    projectivePrimeRatioCoordinate_represents p (some a) ha
  have hbd : projectiveFieldPoint (E := E) z hz ∈
      projectiveClosureSet (L := E) (primeQuotientCoordinate Q) := by rw [hrep]; exact hboundary
  have hlin (i k : Fin 4)
      (h : segreRulingLinearPolynomial (genericOutputValue H E j.castSucc / genericOutputValue H E 0)
        i k ∈ p.asHomogeneousIdeal) :
      z (some i) - algebraMap E κ (genericOutputValue H E j.castSucc / genericOutputValue H E 0) *
        z (some k) = 0 := by
    rw [← hrep] at h
    have he := (projectiveFieldPoint_homogeneous_mem z hz _
      (segreRulingLinearPolynomial_homogeneous _ i k)).mp h
    simpa only [segreRulingLinearPolynomial, map_sub, map_mul, aeval_X, aeval_C] using he
  have h0 := hlin j.castSucc 0 hR0
  have h1 := hlin 3 (if j = 1 then 2 else 1) hR1
  have hkernel : segreRulingMatrix j
      (algebraMap E κ (genericOutputValue H E j.castSucc / genericOutputValue H E 0)) *ᵥ
        (fun i => z (some i)) = 0 := by
    rw [segreRulingMatrix_mulVec]
    fin_cases j
    · exact False.elim (hj rfl)
    · funext i
      fin_cases i
      · simpa using h0
      · simpa using h1
    · funext i
      fin_cases i
      · simpa using h0
      · simpa using h1
  have halg := original_segre_geometric_boundary_coordinates_algebraic_over_ruling_parameter
    H hd hH hN hrank hind I hSegre E Q hQ j hj κ z hz a hnorm hbd hkernel
  let J := segreProjectiveRulingParameterField K (genericOutputValue H E) j p a
  let B := IntermediateField.adjoin J (Set.range (fun i : Fin 4 => z (some i)))
  have hfinite : Module.Finite J B := IntermediateField.finiteDimensional_adjoin (by
    rintro x ⟨i, rfl⟩
    exact (halg i).isIntegral)
  exact ⟨a, ha, B, hfinite, fun i => IntermediateField.subset_adjoin J _ ⟨i, rfl⟩⟩

end DimensionFourDependence
