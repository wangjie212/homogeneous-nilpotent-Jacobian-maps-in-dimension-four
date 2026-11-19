import DimensionFourDependence.AlgebraicProjectivePointLift
import DimensionFourDependence.ProjectivePrimeBaseExtension

/-! # Normalized lifts retain the exact original boundary prime and frame -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pin the canonical field structure before a concrete native
coefficient field is unfolded during instance search. -/
@[instance_reducible]
noncomputable def projectivePrimeRatioFieldField
    {F τ : Type*} [Field F] (q : ProjectiveSpectrum (homogeneousSubmodule τ F)) (a : τ) :
    Field (projectivePrimeRatioField q a) := inferInstance

/-- Pin the canonical coefficient action on a normalized prime field
before a concrete intermediate-field realization is unfolded. -/
@[instance_reducible]
noncomputable def projectivePrimeRatioFieldCoefficientAlgebra
    {F τ : Type*} [Field F] (q : ProjectiveSpectrum (homogeneousSubmodule τ F)) (a : τ) :
    Algebra F (projectivePrimeRatioField q a) := inferInstance

/-- A specified unit coordinate stays outside the complete projective
point ideal, over any coefficient and coordinate-field realization. -/
theorem projectiveFieldPointIdeal_X_not_mem_of_coordinate_eq_one
    {E F τ : Type*} [Field E] [Field F] [Algebra E F]
    (x : τ → F) (a : τ) (ha : x a = 1) :
    X a ∉ (projectiveFieldPointIdeal (E := E) x).toIdeal := by
  intro hm
  have he := (projectiveFieldPointIdeal_mem_homogeneous x (X a) (isHomogeneous_X (R := E) a)).mp hm
  rw [aeval_X] at he
  exact one_ne_zero (ha.symm.trans he)

variable {C A σ : Type*} [Field C] [Field A] [Algebra C A]

/-- The normalized coordinate field of a lifted prime retains exactly
the original homogeneous point ideal after contracting coefficients. -/
theorem projectivePrimeRatioCoordinate_original_ideal_of_contraction
    (p : ProjectiveSpectrum (homogeneousSubmodule σ C))
    (q : ProjectiveSpectrum (homogeneousSubmodule σ A))
    (hcontract : q.asHomogeneousIdeal.toIdeal.comap (MvPolynomial.map (algebraMap C A)) =
      p.asHomogeneousIdeal.toIdeal)
    (a : σ) (ha : X a ∉ q.asHomogeneousIdeal) :
    letI : Algebra C (projectivePrimeRatioField q a) :=
      ((algebraMap A (projectivePrimeRatioField q a)).comp (algebraMap C A)).toAlgebra
    (projectiveFieldPointIdeal (E := C) (projectivePrimeRatioCoordinate q a)).toIdeal =
      p.asHomogeneousIdeal.toIdeal := by
  letI : Algebra C (projectivePrimeRatioField q a) :=
    ((algebraMap A (projectivePrimeRatioField q a)).comp (algebraMap C A)).toAlgebra
  letI : IsScalarTower C A (projectivePrimeRatioField q a) := IsScalarTower.of_algebraMap_eq' rfl
  have hrep := congrArg (fun z => z.asHomogeneousIdeal.toIdeal)
    (projectivePrimeRatioCoordinate_represents q a ha)
  change (projectiveFieldPointIdeal (E := A) (projectivePrimeRatioCoordinate q a)).toIdeal =
    q.asHomogeneousIdeal.toIdeal at hrep
  rw [← projectiveFieldPointIdeal_coefficient_comap (E := A), hrep]
  exact hcontract

variable {G : Type*} [Field G] [Algebra A G] [Algebra C G] [IsScalarTower C A G]

/-- A specified original point at infinity lifts to the chosen algebraic
coefficient realization with exactly the same original homogeneous ideal.
Its specified nonzero source-coordinate label remains the unit frame. -/
theorem specified_projective_infinity_lifts_with_same_original_coordinate_ideal
    [Algebra.IsAlgebraic C A] (v : σ → G)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option σ) C))
    (hp : p ∈ projectiveClosureSet (L := C) v)
    (hzero : X none ∈ p.asHomogeneousIdeal) (a : σ)
    (ha : X (some a) ∉ p.asHomogeneousIdeal) :
    ∃ q : ProjectiveSpectrum (homogeneousSubmodule (Option σ) A),
      q.asHomogeneousIdeal.toIdeal.comap (MvPolynomial.map (algebraMap C A)) =
        p.asHomogeneousIdeal.toIdeal ∧
      X none ∈ q.asHomogeneousIdeal ∧
      ∃ hqa : X (some a) ∉ q.asHomogeneousIdeal,
        (letI : Algebra C (projectivePrimeRatioField q (some a)) :=
          ((algebraMap A (projectivePrimeRatioField q (some a))).comp (algebraMap C A)).toAlgebra;
          (projectiveFieldPointIdeal (E := C) (projectivePrimeRatioCoordinate q (some a))).toIdeal =
            p.asHomogeneousIdeal.toIdeal) ∧
        projectiveFieldPoint (E := A) (projectivePrimeRatioCoordinate q (some a))
          (projectivePrimeRatioCoordinate_ne_zero q (some a) hqa) ∈ projectiveClosureSet (L := A) v ∧
        projectivePrimeRatioCoordinate q (some a) none = 0 ∧
        projectivePrimeRatioCoordinate q (some a) (some a) = 1 := by
  obtain ⟨q, hq, hcontract⟩ := specified_projective_point_lifts_algebraic_coefficients (A := A) v p hp
  have hX (i : Option σ) : X i ∈ q.asHomogeneousIdeal ↔ X i ∈ p.asHomogeneousIdeal := by
    change X i ∈ q.asHomogeneousIdeal.toIdeal ↔ X i ∈ p.asHomogeneousIdeal.toIdeal
    rw [← hcontract]
    change X i ∈ q.asHomogeneousIdeal.toIdeal ↔
      MvPolynomial.map (algebraMap C A) (X i) ∈ q.asHomogeneousIdeal.toIdeal
    rw [MvPolynomial.map_X]
  have hqa : X (some a) ∉ q.asHomogeneousIdeal := fun hm => ha ((hX (some a)).mp hm)
  have hq0 : X none ∈ q.asHomogeneousIdeal := (hX none).mpr hzero
  refine ⟨q, hcontract, hq0, hqa,
    projectivePrimeRatioCoordinate_original_ideal_of_contraction p q hcontract (some a) hqa, ?_,
    projectivePrimeRatioCoordinate_zero_of_mem q (some a) none hq0,
    projectivePrimeRatioCoordinate_self q (some a) hqa⟩
  rw [projectivePrimeRatioCoordinate_represents q (some a) hqa]
  exact hq

/-- If the normalized coordinates of a projective prime are an actual
original closure point, the prime contains every extended original cone
relation over its own coefficient field. -/
theorem normalized_projective_prime_contains_extended_original_cone
    {L F κ τ : Type*} [Field L] [Field F] [Field κ] [Algebra L F] [Algebra L κ]
    (x : τ → κ) (q : ProjectiveSpectrum (homogeneousSubmodule (Option τ) F))
    (a : Option τ) (ha : X a ∉ q.asHomogeneousIdeal) :
    letI : Algebra L (projectivePrimeRatioField q a) :=
      ((algebraMap F (projectivePrimeRatioField q a)).comp (algebraMap L F)).toAlgebra
    projectiveFieldPoint (E := L) (projectivePrimeRatioCoordinate q a)
      (projectivePrimeRatioCoordinate_ne_zero q a ha) ∈ projectiveClosureSet (L := L) x →
    extendCoefficientIdeal F (projectiveConeIdeal (L := L) x) ≤ q.asHomogeneousIdeal.toIdeal := by
  letI : Algebra L (projectivePrimeRatioField q a) :=
    ((algebraMap F (projectivePrimeRatioField q a)).comp (algebraMap L F)).toAlgebra
  letI : IsScalarTower L F (projectivePrimeRatioField q a) := IsScalarTower.of_algebraMap_eq' rfl
  intro hpoint
  rw [projectiveClosureSet_eq_zeroLocus_cone] at hpoint
  have hrep := congrArg (fun z => z.asHomogeneousIdeal.toIdeal)
    (projectivePrimeRatioCoordinate_represents q a ha)
  change (projectiveFieldPointIdeal (E := F) (projectivePrimeRatioCoordinate q a)).toIdeal =
    q.asHomogeneousIdeal.toIdeal at hrep
  rw [← hrep]
  apply Ideal.map_le_iff_le_comap.mpr
  intro P hP
  have hz := hpoint hP
  change projectiveFieldPointMap (E := L) (projectivePrimeRatioCoordinate q a) P = 0 at hz
  change projectiveFieldPointMap (E := F) (projectivePrimeRatioCoordinate q a)
    (MvPolynomial.map (algebraMap L F) P) = 0
  rwa [projectiveFieldPointMap_coefficient_extension]

end DimensionFourDependence
