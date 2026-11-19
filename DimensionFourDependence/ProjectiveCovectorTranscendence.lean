import DimensionFourDependence.GaussImageDimension
import Mathlib.FieldTheory.AlgebraicClosure

/-! # A positive-dimensional normal image has a transcendental coordinate ratio

If all original normal-coordinate ratios were algebraic, their entire
actual generated projective-image field would be algebraic. Positive
transcendence degree therefore supplies a genuine moving coefficient
ratio. A finite coordinate permutation puts any chosen distinct
numerator and denominator into the specified ternary line chart.
-/

namespace DimensionFourDependence

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

/-- Positive dimension of the actual original normal-ratio field
constructs a transcendental normal-coordinate ratio. -/
theorem projective_ratio_positive_dimension_exists_transcendental_coordinate
    (nu : Fin n → L) (j : Fin n)
    (hdim : Algebra.trdeg K (projectiveRatioField (K := K) nu j) ≠ 0) :
    ∃ i : Fin n, Transcendental K (nu i / nu j) := by
  by_contra hn
  simp only [not_exists, Transcendental, not_not] at hn
  have hcoords : ∀ x ∈ Set.range (fun i => nu i / nu j), IsAlgebraic K x := by
    rintro x ⟨i, rfl⟩
    exact hn i
  let : Algebra.IsAlgebraic K (projectiveRatioField (K := K) nu j) :=
    (IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic (F := K) (E := L)).mpr hcoords
  exact hdim trdeg_eq_zero

/-- Any two distinct ternary indices are the first and last entries
of an explicitly constructed original-coordinate permutation. -/
theorem exists_ternary_permutation_first_last (i j : Fin 3) (hij : i ≠ j) :
    ∃ p : Equiv.Perm (Fin 3), p 0 = i ∧ p 2 = j := by
  let q : Equiv.Perm (Fin 3) := Equiv.swap 2 j
  have hqi : q i ≠ 2 := by
    intro he
    have he' := congrArg q he
    apply hij
    simpa [q] using he'
  let r : Equiv.Perm (Fin 3) := Equiv.swap 0 (q i)
  have hr2 : r 2 = 2 := by
    simp only [r, Equiv.swap_apply_def,
      ite_eq_right (show (2 : Fin 3) ≠ 0 by decide), ite_eq_right (Ne.symm hqi)]
  refine ⟨r.trans q, ?_, ?_⟩
  · simp [r, q]
  · change q (r 2) = j
    rw [hr2]
    simp [q]

end DimensionFourDependence
