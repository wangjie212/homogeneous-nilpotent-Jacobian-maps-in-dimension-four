import DimensionFourDependence.ParabolaCoordinateAlgebra
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Parabolas under compatible field embeddings

The original independent directions remain independent after embedding
the coefficient field. Over algebraically closed target coefficients,
nonlinearity of the target coordinates forces the mapped parameter to
remain transcendental. Thus the entire quadratic parametrization passes
to the actual target coordinates.
-/

namespace DimensionFourDependence

open Matrix

variable {L E : Type*} [Field L] [Field E]

/-- A left inverse for the two original directions also proves their
independence after any field embedding. -/
theorem independent_direction_pair_field_map (g : L →+* E)
    (b c : Fin 4 → L) (hbc : LinearIndependent L ![b, c]) :
    LinearIndependent E ![g ∘ b, g ∘ c] := by
  classical
  obtain ⟨C, hC⟩ := directionPlaneMatrix_has_left_inverse b c hbc
  have hCE : C.map g * directionPlaneMatrix (g ∘ b) (g ∘ c) = 1 := by
    have hB : (directionPlaneMatrix b c).map g =
        directionPlaneMatrix (g ∘ b) (g ∘ c) := by
      funext i j
      fin_cases j <;> rfl
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) L => M.map g) hC
    simpa [Matrix.map_mul, hB] using he
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have hz : directionPlaneMatrix (g ∘ b) (g ∘ c) *ᵥ a = 0 := by
    funext j
    have hj := congrFun ha j
    simpa only [Matrix.mulVec, dotProduct, directionPlaneMatrix, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, mul_comm, Pi.zero_apply] using hj
  have he := congrArg (fun z => C.map g *ᵥ z) hz
  rw [Matrix.mulVec_mulVec, hCE, Matrix.one_mulVec, Matrix.mulVec_zero] at he
  exact congrFun he i

variable {F G : Type*} [Field F] [Field G] [Algebra L F] [Algebra E G]

/-- Algebraic elements of an extension of algebraically closed
coefficients have actual coefficient-field preimages. -/
theorem algebraic_value_preimage_of_isAlgClosed [IsAlgClosed E]
    (z : G) (hz : IsAlgebraic E z) : ∃ r : E, algebraMap E G r = z := by
  have hmem := mem_algebraicClosure_iff.mpr hz
  have hbot : algebraicClosure E G = ⊥ :=
    IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
  rw [hbot] at hmem
  exact hmem

/-- Compatible field embeddings retain the specified original
quadratic expressions, with their actual mapped parameter. -/
theorem quadratic_expression_map_of_compatible
    (f : F →+* G) (g : L →+* E)
    (hcomp : ∀ l : L, algebraMap E G (g l) = f (algebraMap L F l))
    (x : Fin 4 → F) (a b c : Fin 4 → L) (t : F)
    (hx : ∀ i, x i = algebraMap L F (a i) + algebraMap L F (b i) * t +
      algebraMap L F (c i) * t ^ 2) :
    ∀ i, (f ∘ x) i = algebraMap E G ((g ∘ a) i) +
      algebraMap E G ((g ∘ b) i) * f t + algebraMap E G ((g ∘ c) i) * (f t) ^ 2 := by
  intro i
  change f (x i) = algebraMap E G (g (a i)) + algebraMap E G (g (b i)) * f t +
    algebraMap E G (g (c i)) * (f t) ^ 2
  rw [hcomp, hcomp, hcomp]
  simpa only [map_add, map_mul, map_pow] using congrArg f (hx i)

/-- A nonlinear target over algebraically closed coefficients retains
the actual parabola, including its independent directions and parameter. -/
theorem LiesInAffineParabola.map_of_compatible_of_nonlinear [IsAlgClosed E]
    (f : F →+* G) (g : L →+* E)
    (hcomp : ∀ l : L, algebraMap E G (g l) = f (algebraMap L F l))
    (x : Fin 4 → F) (hx : LiesInAffineParabola (L := L) x)
    (hline : ¬ LiesInAffineLine (E := E) (f ∘ x)) :
    LiesInAffineParabola (L := E) (f ∘ x) := by
  obtain ⟨a, b, c, hbc, t, _ht, hpoint⟩ := hx
  have hmap := quadratic_expression_map_of_compatible f g hcomp x a b c t hpoint
  refine ⟨g ∘ a, g ∘ b, g ∘ c, independent_direction_pair_field_map g b c hbc,
    f t, ?_, hmap⟩
  intro halg
  obtain ⟨r, hr⟩ := algebraic_value_preimage_of_isAlgClosed (f t) halg
  apply hline
  refine ⟨fun i => g (a i) + g (b i) * r + g (c i) * r ^ 2,
    (fun _ => 1 : Fin 4 → E), ?_, 0, ?_⟩
  · intro hz
    have h := congrFun hz 0
    simp only [Pi.zero_apply, one_ne_zero] at h
  · intro i
    simpa only [Function.comp_apply, map_add, map_mul, map_pow, map_one,
      mul_zero, add_zero, hr] using hmap i

end DimensionFourDependence
