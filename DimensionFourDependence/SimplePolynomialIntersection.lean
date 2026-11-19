import DimensionFourDependence.SimplePolynomialLocalAlgebra

/-! # Actual polynomial simple-root intersections and their local quotients

For the original polynomial P through the origin, localize the actual
quotient F[u,v]/(u^2,P) at the origin prime. A nonzero transverse first
derivative proves that its dimension and local intersection length are
exactly two. Any local algebra presented as a quotient of this actual
intersection has dimension and length at most two.
-/

namespace DimensionFourDependence

open MvPolynomial Module

variable {F : Type*} [Field F]

/-- The original doubled-line intersection ideal, without a coefficient expansion. -/
noncomputable def simplePolynomialIntersectionIdeal (P : MvPolynomial (Fin 2) F) :
    Ideal (MvPolynomial (Fin 2) F) := Ideal.span {X 0 ^ 2, P}

/-- The original polynomial equations construct their rational origin prime. -/
theorem simplePolynomialIntersectionIdeal_origin (P : MvPolynomial (Fin 2) F)
    (hP : aeval (fun _ : Fin 2 => (0 : F)) P = 0) :
    simplePolynomialIntersectionIdeal P ≤ RingHom.ker (aeval (fun _ : Fin 2 => (0 : F))).toRingHom := by
  apply Ideal.span_le.mpr
  rintro p (rfl | rfl)
  · change aeval (fun _ : Fin 2 => (0 : F)) (X 0 ^ 2) = 0
    simp
  · exact hP

/-- The actual quotient localization of the original two equations at the origin. -/
noncomputable abbrev simplePolynomialIntersectionLocalRing (P : MvPolynomial (Fin 2) F)
    (hP : aeval (fun _ : Fin 2 => (0 : F)) P = 0) :=
  Localization.AtPrime (zeroPointQuotientPrime (simplePolynomialIntersectionIdeal P)
    (simplePolynomialIntersectionIdeal_origin P hP))

/-- The two original affine coordinates in the actual local intersection. -/
noncomputable def simplePolynomialLocalCoordinate (P : MvPolynomial (Fin 2) F)
    (hP : aeval (fun _ : Fin 2 => (0 : F)) P = 0) (i : Fin 2) :
    simplePolynomialIntersectionLocalRing P hP :=
  zeroPointLocalCoordinate (simplePolynomialIntersectionIdeal P) (simplePolynomialIntersectionIdeal_origin P hP) i

/-- Both polynomial equations hold in their actual quotient localization. -/
theorem simplePolynomialLocal_equations (P : MvPolynomial (Fin 2) F)
    (hP : aeval (fun _ : Fin 2 => (0 : F)) P = 0) :
    (simplePolynomialLocalCoordinate P hP 0) ^ 2 = 0 ∧
      aeval ![simplePolynomialLocalCoordinate P hP 0, simplePolynomialLocalCoordinate P hP 1] P = 0 := by
  let J := simplePolynomialIntersectionIdeal P
  let hJ := simplePolynomialIntersectionIdeal_origin P hP
  have hhom : aeval ![simplePolynomialLocalCoordinate P hP 0, simplePolynomialLocalCoordinate P hP 1] =
      zeroPointLocalPolynomialHom J hJ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [zeroPointLocalPolynomialHom_X, simplePolynomialLocalCoordinate, J]
  constructor
  · have hh := zeroPointLocalPolynomialHom_relation J hJ (X 0 ^ 2) (Ideal.subset_span (by simp))
    simpa only [map_pow, zeroPointLocalPolynomialHom_X, simplePolynomialLocalCoordinate] using hh
  · rw [hhom]
    exact zeroPointLocalPolynomialHom_relation J hJ P (Ideal.subset_span (by simp))

/-- The two original local coordinates generate the entire maximal ideal. -/
theorem simplePolynomialLocal_maximalIdeal (P : MvPolynomial (Fin 2) F)
    (hP : aeval (fun _ : Fin 2 => (0 : F)) P = 0) :
    IsLocalRing.maximalIdeal (simplePolynomialIntersectionLocalRing P hP) =
      Ideal.span {simplePolynomialLocalCoordinate P hP 0, simplePolynomialLocalCoordinate P hP 1} := by
  rw [zeroPointLocal_maximalIdeal]
  congr 1
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [simplePolynomialLocalCoordinate]
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- The nonzero original transverse derivative gives the length bound
for the actual local intersection, without a supplied local model. -/
theorem simple_polynomial_intersection_local_dimension_and_length_le_two
    (P : MvPolynomial (Fin 2) F) (hP : aeval (fun _ : Fin 2 => (0 : F)) P = 0)
    (hPv : aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 P) ≠ 0) :
    Module.Finite F (simplePolynomialIntersectionLocalRing P hP) ∧
      finrank F (simplePolynomialIntersectionLocalRing P hP) ≤ 2 ∧
      Module.length (simplePolynomialIntersectionLocalRing P hP) (simplePolynomialIntersectionLocalRing P hP) ≤ 2 := by
  have heq := simplePolynomialLocal_equations P hP
  exact simple_polynomial_double_line_local_dimension_and_length_le_two
    (zeroPointLocalEvaluation (simplePolynomialIntersectionIdeal P) (simplePolynomialIntersectionIdeal_origin P hP))
    (simplePolynomialLocalCoordinate P hP 0) (simplePolynomialLocalCoordinate P hP 1)
    (zeroPointLocalEvaluation_coordinate _ _ 0) (zeroPointLocalEvaluation_coordinate _ _ 1)
    (simplePolynomialLocal_maximalIdeal P hP) heq.1 P hP hPv heq.2

/-- The original first-derivative equations prove that the doubled-line
coordinate survives in the actual localized quotient. -/
theorem simplePolynomialLocal_doubled_coordinate_ne_zero
    (P : MvPolynomial (Fin 2) F) (hP : aeval (fun _ : Fin 2 => (0 : F)) P = 0)
    (hPv : aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 P) ≠ 0) :
    simplePolynomialLocalCoordinate P hP 0 ≠ 0 := by
  intro hu
  let J := simplePolynomialIntersectionIdeal P
  let hJ := simplePolynomialIntersectionIdeal_origin P hP
  let q := zeroPointQuotientPrime J hJ
  change algebraMap (MvPolynomial (Fin 2) F ⧸ J) (Localization.AtPrime q)
    (Ideal.Quotient.mk J (X 0)) = 0 at hu
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) _).mp hu
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (t : MvPolynomial (Fin 2) F ⧸ J)
  have hmem : s * X 0 ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul, hs]
    exact ht
  have hs0 := binary_simple_root_coordinate_annihilator_vanishes P hP hPv s hmem
  have hden : zeroPointQuotientEvaluation J hJ (t : MvPolynomial (Fin 2) F ⧸ J) ≠ 0 := t.property
  apply hden
  rw [← hs]
  change aeval (fun _ : Fin 2 => (0 : F)) s = 0
  exact hs0

/-- The actual local intersection has dimension and length exactly two
from the original polynomial's simple transverse root. -/
theorem simple_polynomial_intersection_local_exact_multiplicity_two
    (P : MvPolynomial (Fin 2) F) (hP : aeval (fun _ : Fin 2 => (0 : F)) P = 0)
    (hPv : aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 P) ≠ 0) :
    Module.Finite F (simplePolynomialIntersectionLocalRing P hP) ∧
      finrank F (simplePolynomialIntersectionLocalRing P hP) = 2 ∧
      Module.length (simplePolynomialIntersectionLocalRing P hP) (simplePolynomialIntersectionLocalRing P hP) = 2 := by
  have hbound := simple_polynomial_intersection_local_dimension_and_length_le_two P hP hPv
  have hu : simplePolynomialLocalCoordinate P hP 0 ∈
      IsLocalRing.maximalIdeal (simplePolynomialIntersectionLocalRing P hP) := by
    rw [simplePolynomialLocal_maximalIdeal]
    exact Ideal.subset_span (by simp)
  have hge := nonzero_maximal_ideal_element_local_length_ge_two (simplePolynomialLocalCoordinate P hP 0)
    hu (simplePolynomialLocal_doubled_coordinate_ne_zero P hP hPv)
  have hlen := le_antisymm hbound.2.2 hge
  let := hbound.1
  have hle := local_algebra_length_le_coefficient_dimension (F := F)
    (A := simplePolynomialIntersectionLocalRing P hP)
  rw [hlen] at hle
  have hdim : 2 ≤ finrank F (simplePolynomialIntersectionLocalRing P hP) := by exact_mod_cast hle
  exact ⟨hbound.1, Nat.le_antisymm hbound.2.1 hdim, hlen⟩

variable {B : Type*} [CommRing B] [Algebra F B] [IsLocalRing B]

omit [IsLocalRing B] in
/-- Every actual local quotient of the polynomial intersection inherits
its dimension and local length bound, as required for a closed fiber subscheme. -/
theorem simple_polynomial_intersection_local_quotient_bound
    (P : MvPolynomial (Fin 2) F) (hP : aeval (fun _ : Fin 2 => (0 : F)) P = 0)
    (hPv : aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 P) ≠ 0)
    (phi : simplePolynomialIntersectionLocalRing P hP →ₐ[F] B) (hsurj : Function.Surjective phi) :
    Module.Finite F B ∧ finrank F B ≤ 2 ∧ Module.length B B ≤ 2 := by
  have hsource := simple_polynomial_intersection_local_exact_multiplicity_two P hP hPv
  let := hsource.1
  have hfinite : Module.Finite F B := Module.Finite.of_surjective phi.toLinearMap hsurj
  let := hfinite
  have hdim := LinearMap.finrank_le_finrank_of_surjective (f := phi.toLinearMap) hsurj
  rw [hsource.2.1] at hdim
  exact ⟨hfinite, hdim, (local_algebra_length_le_coefficient_dimension (F := F) (A := B)).trans
    (by exact_mod_cast hdim)⟩

end DimensionFourDependence
