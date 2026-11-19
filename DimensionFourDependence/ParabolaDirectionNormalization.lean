import DimensionFourDependence.ParabolicFiberDerivation
import Mathlib.FieldTheory.AlgebraicClosure

/-! # Normalize an actual projected parabola direction inside the same geometric constants -/

namespace DimensionFourDependence

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

/-- Multiplication by a nonzero geometric constant preserves the
actual transcendental fiber parameter. -/
theorem transcendental_parameter_mul_nonzero_constant
    (t : F) (ht : Transcendental E t) (a : E) (ha : a ≠ 0) :
    Transcendental E (algebraMap E F a * t) := by
  intro halg
  have hquot : IsAlgebraic E ((algebraMap E F a * t) / algebraMap E F a) :=
    mem_algebraicClosure_iff.mp ((algebraicClosure E F).div_mem
      (mem_algebraicClosure_iff.mpr halg)
      (mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap a)))
  have haF : algebraMap E F a ≠ 0 := by simpa only [map_zero] using (algebraMap E F).injective.ne ha
  have he : (algebraMap E F a * t) / algebraMap E F a = t := by field_simp [haF]
  rw [he] at hquot
  exact ht hquot

/-- Rescaling only the actual fiber parameter normalizes any nonzero
projected direction coordinate to one. Its vertex coefficient becomes
C/A_j^2 and stays nonzero, over the same geometric constant field. -/
theorem actual_vertex_parabola_normalizes_projected_direction
    (t : F) (ht : Transcendental E t) (z : Fin 4 → F) (x A : Fin 3 → E) (w B C : E)
    (hC : C ≠ 0) (j : Fin 3) (hj : A j ≠ 0)
    (hline : ∀ i : Fin 3, z i.castSucc = algebraMap E F (x i) + algebraMap E F (A i) * t)
    (hparabola : z (Fin.last 3) = algebraMap E F w + algebraMap E F B * t + algebraMap E F C * t ^ 2) :
    Transcendental E (algebraMap E F (A j) * t) ∧ A j / A j = 1 ∧ C / (A j) ^ 2 ≠ 0 ∧
      (∀ i : Fin 3, z i.castSucc = algebraMap E F (x i) + algebraMap E F (A i / A j) *
        (algebraMap E F (A j) * t)) ∧
      z (Fin.last 3) = algebraMap E F w + algebraMap E F (B / A j) * (algebraMap E F (A j) * t) +
        algebraMap E F (C / (A j) ^ 2) * (algebraMap E F (A j) * t) ^ 2 := by
  have hjF : algebraMap E F (A j) ≠ 0 := by simpa only [map_zero] using (algebraMap E F).injective.ne hj
  refine ⟨transcendental_parameter_mul_nonzero_constant t ht (A j) hj, div_self hj,
    div_ne_zero hC (pow_ne_zero 2 hj), ?_, ?_⟩
  · intro i
    rw [hline, map_div₀]
    field_simp [hjF]
  · rw [hparabola, map_div₀, map_div₀, map_pow]
    field_simp [hjF]

end DimensionFourDependence
