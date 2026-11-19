import DimensionFourDependence.HomogeneousPrincipalHilbert
import DimensionFourDependence.FiberHilbertDegree

/-! # A projected plane equation has no larger degree than the original curve

The exact principal Hilbert identity compares the equation degree with
the original curve's actual eventual Hilbert slope. A zero equation is
also excluded by its quadratic Hilbert growth. No plane-curve degree
classification or nondegeneracy bound is assumed.
-/

namespace DimensionFourDependence

open MvPolynomial Module

variable {L sigma tau : Type*} [Field L]

/-- With no equations, the actual quotient is the full homogeneous space. -/
theorem projectiveHilbertFunction_bot_eq [Finite sigma] (n : ℕ) :
    projectiveHilbertFunction (⊥ : Ideal (MvPolynomial sigma L)) n =
      finrank L (homogeneousSubmodule sigma L n) := by
  have hrel : homogeneousRelationSpace (⊥ : Ideal (MvPolynomial sigma L)) n = ⊥ := by
    ext P
    change (P : MvPolynomial sigma L) = 0 ↔ P = 0
    exact ⟨fun he => Subtype.ext he, fun he => congrArg Subtype.val he⟩
  have he := projectiveHilbertFunction_add_relation_finrank (⊥ : Ideal (MvPolynomial sigma L)) n
  have hdim : finrank L (homogeneousRelationSpace (⊥ : Ideal (MvPolynomial sigma L)) n) = 0 := by
    rw [hrel]
    exact finrank_bot L _
  omega

/-- A plane projection of a curve with linear Hilbert growth has a
nonzero equation; the zero ideal would have quadratic Hilbert growth. -/
theorem plane_principal_equation_ne_zero_of_curve_hilbert_bound
    [Finite sigma] [Finite tau] (hcard : Nat.card sigma = 3)
    (P : MvPolynomial sigma L) (I : Ideal (MvPolynomial tau L))
    {e : ℕ} (he : HasCurveHilbertDegree I e)
    (hbound : ∀ n, projectiveHilbertFunction (Ideal.span {P}) n ≤ projectiveHilbertFunction I n) :
    P ≠ 0 := by
  intro hP
  subst P
  obtain ⟨_hepos, b, N, hN⟩ := he
  let n := N + 2 * e + 2 * b.natAbs + 3
  have hn : N ≤ n := by dsimp only [n]; omega
  have hlin := hN n hn
  have hb := hbound n
  rw [Ideal.span_singleton_zero, projectiveHilbertFunction_bot_eq] at hb
  have hquad := twice_plane_homogeneous_piece_finrank (L := L) hcard n
  have hh : (2 : ℤ) * (finrank L (homogeneousSubmodule sigma L n) : ℤ) ≤
      2 * (projectiveHilbertFunction I n : ℤ) := by exact_mod_cast Nat.mul_le_mul_left 2 hb
  rw [hlin] at hh
  have hquad' : (2 : ℤ) * (finrank L (homogeneousSubmodule sigma L n) : ℤ) =
      ((n : ℤ) + 2) * ((n : ℤ) + 1) := by exact_mod_cast hquad
  rw [hquad'] at hh
  have hbig : 2 * (e : ℤ) + 2 * (b.natAbs : ℤ) + 3 ≤ (n : ℤ) := by
    dsimp only [n]
    push_cast
    omega
  have hn1 : (1 : ℤ) ≤ n := by omega
  have hprod : (2 * (e : ℤ) + 2 * (b.natAbs : ℤ) + 3) * n ≤ (n : ℤ) * n := by
    nlinarith
  have habs : (b.natAbs : ℤ) ≤ (b.natAbs : ℤ) * n := by
    nlinarith [Int.natCast_nonneg b.natAbs]
  nlinarith [show b ≤ (b.natAbs : ℤ) from Int.le_natAbs]

/-- A nonzero homogeneous plane equation's degree is bounded by the
actual Hilbert degree of any curve whose Hilbert function dominates its quotient. -/
theorem plane_principal_equation_degree_le_curve_degree
    [Finite sigma] [Finite tau] (hcard : Nat.card sigma = 3)
    (P : MvPolynomial sigma L) {d : ℕ} (hP : P.IsHomogeneous d) (hP0 : P ≠ 0)
    (I : Ideal (MvPolynomial tau L)) {e : ℕ} (he : HasCurveHilbertDegree I e)
    (hbound : ∀ n, projectiveHilbertFunction (Ideal.span {P}) n ≤ projectiveHilbertFunction I n) :
    d ≤ e := by
  by_contra hde
  have hlt : e + 1 ≤ d := by omega
  obtain ⟨_hepos, b, N, hN⟩ := he
  let n := N + e * d + b.natAbs + 1
  have hn : N ≤ n + d := by dsimp only [n]; omega
  have hlin := hN (n + d) hn
  have hb := hbound (n + d)
  have heq := plane_principal_hilbert_twice hcard P hP hP0 n
  have hh : (2 : ℤ) * (projectiveHilbertFunction (Ideal.span {P}) (n + d) : ℤ) ≤
      2 * (projectiveHilbertFunction I (n + d) : ℤ) := by exact_mod_cast Nat.mul_le_mul_left 2 hb
  rw [hlin] at hh
  have heq' : (2 : ℤ) * (projectiveHilbertFunction (Ideal.span {P}) (n + d) : ℤ) =
      (d : ℤ) * (2 * (n : ℤ) + d + 3) := by exact_mod_cast heq
  rw [heq'] at hh
  push_cast at hh
  have hbig : (e : ℤ) * d + (b.natAbs : ℤ) + 1 ≤ (n : ℤ) := by
    dsimp only [n]
    push_cast
    omega
  have hlt' : (e : ℤ) + 1 ≤ d := by exact_mod_cast hlt
  have hprod : 0 ≤ ((d : ℤ) - e - 1) * n :=
    mul_nonneg (by omega) (Int.natCast_nonneg n)
  have hquad : 0 ≤ (d : ℤ) * (d + 3) := by positivity
  nlinarith [show b ≤ (b.natAbs : ℤ) from Int.le_natAbs]

end DimensionFourDependence
