import DimensionFourDependence.DoubleLinePolynomialLocalModel
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # The polynomial doubled-line intersection has exact local multiplicity two

The two first partial derivatives at the origin prove that a polynomial
whose product with u belongs to (u^2,G) must vanish at the origin.
Consequently u survives localization at that point. The actual local
quotient therefore has dimension and module length exactly two when
the linear v coefficient of G is nonzero.
-/

namespace DimensionFourDependence

open MvPolynomial Module

variable {F : Type*} [Field F]

/-- The two first derivatives at the origin retain exactly the two
original linear coefficients of the quadric. -/
theorem doubleLineQuadratic_first_partials (a b c e f : F) :
    aeval (fun _ : Fin 2 => (0 : F)) (pderiv 0 (doubleLineQuadratic a b c e f)) = a ∧
      aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 (doubleLineQuadratic a b c e f)) = b := by
  constructor <;> simp [doubleLineQuadratic, pderiv_X]

/-- A multiple of u cannot vanish in the polynomial intersection
unless its coefficient vanishes at the origin. Both partial derivatives
are used, so all quadratic terms and their multiplicities are retained. -/
theorem doubleLineIntersectionIdeal_coordinate_annihilator_vanishes
    (a b c e f : F) (hb : b ≠ 0) (s : MvPolynomial (Fin 2) F)
    (hs : s * X 0 ∈ doubleLineIntersectionIdeal a b c e f) :
    aeval (fun _ : Fin 2 => (0 : F)) s = 0 := by
  obtain ⟨p, q, hpq⟩ := Ideal.mem_span_pair.mp hs
  have hG : constantCoeff (doubleLineQuadratic a b c e f) = 0 := by
    simp [doubleLineQuadratic]
  have hpartials := doubleLineQuadratic_first_partials a b c e f
  have hdu : constantCoeff (pderiv 0 (doubleLineQuadratic a b c e f)) = a := by simpa using hpartials.1
  have hdv : constantCoeff (pderiv 1 (doubleLineQuadratic a b c e f)) = b := by simpa using hpartials.2
  have h0 := congrArg (fun z : MvPolynomial (Fin 2) F => aeval (fun _ : Fin 2 => (0 : F)) (pderiv 0 z)) hpq
  have h1 := congrArg (fun z : MvPolynomial (Fin 2) F => aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 z)) hpq
  simp [pderiv_X, hG, hdu, hdv] at h0 h1
  have hq : constantCoeff q = 0 := by
    exact h1.resolve_right hb
  simpa [hq] using h0.symm

/-- The doubled-line coordinate survives in the actual quotient
localization at the origin. No nonzero nilpotent is assumed. -/
theorem doubleLineLocalU_ne_zero (a b c e f : F) (hb : b ≠ 0) :
    doubleLineLocalU a b c e f ≠ 0 := by
  intro hu
  let J := doubleLineIntersectionIdeal a b c e f
  let hJ := doubleLineIntersectionIdeal_origin a b c e f
  let q := zeroPointQuotientPrime J hJ
  change algebraMap (MvPolynomial (Fin 2) F ⧸ J)
    (Localization.AtPrime q) (Ideal.Quotient.mk J (X 0)) = 0 at hu
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) _).mp hu
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (t : MvPolynomial (Fin 2) F ⧸ J)
  have hmem : s * X 0 ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul, hs]
    exact ht
  have hs0 := doubleLineIntersectionIdeal_coordinate_annihilator_vanishes a b c e f hb s hmem
  have hden : zeroPointQuotientEvaluation J hJ (t : MvPolynomial (Fin 2) F ⧸ J) ≠ 0 := t.property
  apply hden
  rw [← hs]
  change aeval (fun _ : Fin 2 => (0 : F)) s = 0
  exact hs0

/-- The actual polynomial quotient localized at the origin has exact
intersection length two in the simple-root case. -/
theorem doubleLine_polynomial_local_intersection_length_eq_two
    (a b c e f : F) (hb : b ≠ 0) :
    Module.length (doubleLineIntersectionLocalRing a b c e f)
      (doubleLineIntersectionLocalRing a b c e f) = 2 := by
  have hmem := doubleLineLocal_coordinates_mem_maximalIdeal a b c e f
  have heq := doubleLineLocal_equations a b c e f
  exact simple_root_double_line_local_length_eq_two
    (doubleLineLocalU a b c e f) (doubleLineLocalV a b c e f) hmem.1 hmem.2 a b c e f hb heq.1
    (doubleLineLocalU_ne_zero a b c e f hb) heq.2
    (doubleLineLocal_maximalIdeal a b c e f) (doubleLineLocal_coefficient_residue_surjective a b c e f)

/-- Both dimension and intersection length are exactly two for the
constructed polynomial local intersection algebra. -/
theorem doubleLine_polynomial_local_intersection_exact_multiplicity_two
    (a b c e f : F) (hb : b ≠ 0) :
    Module.Finite F (doubleLineIntersectionLocalRing a b c e f) ∧
      finrank F (doubleLineIntersectionLocalRing a b c e f) = 2 ∧
      Module.length (doubleLineIntersectionLocalRing a b c e f)
        (doubleLineIntersectionLocalRing a b c e f) = 2 := by
  have hbound := doubleLine_polynomial_local_intersection_dimension_and_length_le_two a b c e f hb
  have hlen := doubleLine_polynomial_local_intersection_length_eq_two a b c e f hb
  let := hbound.1
  have hle := local_algebra_length_le_coefficient_dimension (F := F)
    (A := doubleLineIntersectionLocalRing a b c e f)
  rw [hlen] at hle
  have hdim : 2 ≤ finrank F (doubleLineIntersectionLocalRing a b c e f) := by exact_mod_cast hle
  exact ⟨hbound.1, Nat.le_antisymm hbound.2.1 hdim, hlen⟩

end DimensionFourDependence
