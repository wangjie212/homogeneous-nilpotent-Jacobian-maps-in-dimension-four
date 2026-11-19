import DimensionFourDependence.HomogeneousSectionMultiplication

/-! # The actual Hilbert function of one homogeneous equation

Multiplication by a nonzero homogeneous equation identifies each shifted
polynomial space with the corresponding space of principal relations.
In three homogeneous coordinates this gives the exact plane-curve
Hilbert function, with leading coefficient equal to the equation degree.
-/

namespace DimensionFourDependence

open MvPolynomial Module

variable {L sigma : Type*} [Field L]

/-- The image of homogeneous multiplication is exactly the actual
principal relation space in the prescribed degree. -/
theorem homogeneousSectionMultiplication_principal_range
    (P : MvPolynomial sigma L) {d : ℕ} (hP : P.IsHomogeneous d) (n : ℕ) :
    LinearMap.range (homogeneousSectionMultiplication P hP n) =
      homogeneousRelationSpace (Ideal.span ({P} : Set (MvPolynomial sigma L))) (n + d) := by
  ext Q
  constructor
  · rintro ⟨R, rfl⟩
    exact Ideal.mem_span_singleton.mpr ⟨R, rfl⟩
  · intro hQ
    obtain ⟨R, hR⟩ := Ideal.mem_span_singleton.mp hQ
    change (Q : MvPolynomial sigma L) = P * R at hR
    have he := congrArg (homogeneousComponent (n + d)) hR
    rw [homogeneousComponent_mul_of_isHomogeneous hP R n,
      homogeneousComponent_of_mem Q.property, ite_eq_left rfl] at he
    exact ⟨⟨homogeneousComponent n R, homogeneousComponent_isHomogeneous n R⟩,
      Subtype.ext he.symm⟩

/-- A nonzero equation gives injective multiplication in every degree. -/
theorem homogeneousSectionMultiplication_injective
    (P : MvPolynomial sigma L) {d : ℕ} (hP : P.IsHomogeneous d)
    (hP0 : P ≠ 0) (n : ℕ) : Function.Injective (homogeneousSectionMultiplication P hP n) := by
  intro Q R he
  apply Subtype.ext
  exact mul_left_cancel₀ hP0 (congrArg Subtype.val he)

/-- The principal homogeneous Hilbert identity uses the actual
quotient dimensions, without a presumed degree formula. -/
theorem homogeneous_principal_hilbert_identity [Finite sigma]
    (P : MvPolynomial sigma L) {d : ℕ} (hP : P.IsHomogeneous d)
    (hP0 : P ≠ 0) (n : ℕ) :
    projectiveHilbertFunction (Ideal.span ({P} : Set (MvPolynomial sigma L))) (n + d) +
      finrank L (homogeneousSubmodule sigma L n) =
        finrank L (homogeneousSubmodule sigma L (n + d)) := by
  have hdim := LinearMap.finrank_range_of_inj (homogeneousSectionMultiplication_injective P hP hP0 n)
  rw [homogeneousSectionMultiplication_principal_range] at hdim
  rw [← hdim]
  exact projectiveHilbertFunction_add_relation_finrank _ _

/-- Twice the number of degree-n monomials in three variables has
the elementary quadratic form used in the actual Hilbert calculation. -/
theorem twice_plane_homogeneous_piece_finrank
    [Finite sigma] (hcard : Nat.card sigma = 3) (n : ℕ) :
    2 * finrank L (homogeneousSubmodule sigma L n) = (n + 2) * (n + 1) := by
  rw [homogeneousPiece_finrank, hcard]
  have he : 3 + n - 1 = n + 2 := by omega
  rw [he, ← Nat.choose_symm (by omega : n ≤ n + 2)]
  have hn : n + 2 - n = 2 := by omega
  rw [hn]
  have hq := Nat.cast_choose_two (K := ℚ) (n + 2)
  have hr : (2 : ℚ) * ((n + 2).choose 2 : ℚ) = ((n + 2 : ℕ) : ℚ) * ((n + 1 : ℕ) : ℚ) := by
    rw [hq]
    push_cast
    ring
  exact_mod_cast hr

/-- A plane curve's actual principal quotient has eventual linear
Hilbert function with slope equal to its homogeneous equation degree. -/
theorem plane_principal_hilbert_twice
    [Finite sigma] (hcard : Nat.card sigma = 3)
    (P : MvPolynomial sigma L) {d : ℕ} (hP : P.IsHomogeneous d)
    (hP0 : P ≠ 0) (n : ℕ) :
    2 * projectiveHilbertFunction (Ideal.span ({P} : Set (MvPolynomial sigma L))) (n + d) =
      d * (2 * n + d + 3) := by
  have he := homogeneous_principal_hilbert_identity P hP hP0 n
  have h0 := twice_plane_homogeneous_piece_finrank (L := L) hcard n
  have h1 := twice_plane_homogeneous_piece_finrank (L := L) hcard (n + d)
  nlinarith

end DimensionFourDependence
