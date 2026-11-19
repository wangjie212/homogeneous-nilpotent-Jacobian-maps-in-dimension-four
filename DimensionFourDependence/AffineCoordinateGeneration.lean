import DimensionFourDependence.AffinePivotCoordinates

/-! # Original affine generators and equations under an affine pivot change -/

namespace DimensionFourDependence

open MvPolynomial

variable {k A σ : Type*} [Field k] [CommRing A] [Algebra k A]
  [Fintype σ] [DecidableEq σ]

/-- Replace the original pivot coordinate by its given affine linear
form, evaluated in the original affine coordinate algebra. -/
noncomputable def affinePivotCoordinate
    (x : σ → A) (j : σ) (a b : k) (c : σ → k) (i : σ) : A :=
  aeval x (affinePivotSubstitution j a b c (X i))

/-- All nonpivot original coordinates retain their exact values. -/
theorem affinePivotCoordinate_other
    (x : σ → A) (j : σ) (a b : k) (c : σ → k) {i : σ} (hi : i ≠ j) :
    affinePivotCoordinate x j a b c i = x i := by
  simp [affinePivotCoordinate, affinePivotSubstitution, hi]

/-- The new pivot is the specified original affine linear form. -/
theorem affinePivotCoordinate_pivot
    (x : σ → A) (j : σ) (a b : k) (c : σ → k) :
    affinePivotCoordinate x j a b c j =
      algebraMap k A a * x j + (algebraMap k A b +
        ∑ i ∈ Finset.univ.erase j, algebraMap k A (c i) * x i) := by
  simp [affinePivotCoordinate, affinePivotSubstitution, affinePivotRemainder]

/-- Evaluation in the new actual coordinates is composition with the
forward substitution in the original coordinates. -/
theorem aeval_affinePivotCoordinate
    (x : σ → A) (j : σ) (a b : k) (c : σ → k) :
    aeval (affinePivotCoordinate x j a b c) =
      (aeval x).comp (affinePivotSubstitution j a b c) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [aeval_X, AlgHom.comp_apply, affinePivotCoordinate]

/-- Solving for the pivot and evaluating in the new actual coordinates
recovers evaluation of every original polynomial exactly. -/
theorem affinePivotCoordinate_eval_inverse
    (x : σ → A) (j : σ) (a b : k) (c : σ → k) (ha : a ≠ 0)
    (f : MvPolynomial σ k) :
    aeval (affinePivotCoordinate x j a b c) (affinePivotInverseSubstitution j a b c f) =
      aeval x f := by
  rw [aeval_affinePivotCoordinate]
  exact congrArg (aeval x) (AlgHom.congr_fun (affinePivotSubstitution_comp_inverse j a b c ha) f)

/-- An affine pivot change with nonzero coefficient preserves the
original algebra generation, without an assumed inverse point map. -/
theorem affinePivotCoordinate_adjoin_eq_top
    (x : σ → A) (hx : Algebra.adjoin k (Set.range x) = ⊤)
    (j : σ) (a b : k) (c : σ → k) (ha : a ≠ 0) :
    Algebra.adjoin k (Set.range (affinePivotCoordinate x j a b c)) = ⊤ := by
  let y := affinePivotCoordinate x j a b c
  have hmem (i : σ) : x i ∈ Algebra.adjoin k (Set.range y) := by
    have hp : aeval y (affinePivotInverseSubstitution j a b c (X i)) ∈
        Algebra.adjoin k (Set.range y) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨_, rfl⟩
    have heq : aeval y (affinePivotInverseSubstitution j a b c (X i)) = x i := by
      simpa only [aeval_X] using affinePivotCoordinate_eval_inverse x j a b c ha (X i)
    rwa [heq] at hp
  apply top_unique
  rw [← hx]
  apply Algebra.adjoin_le_iff.mpr
  rintro _ ⟨i, rfl⟩
  exact hmem i

end DimensionFourDependence
