import DimensionFourDependence.SegreRulingNilpotenceObstruction
import DimensionFourDependence.NilpotentFunctionalTransport

/-! # The invariant three-space in the reduced Segre tangent lattice -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 3000000

variable {F : Type*} [Field F]

/-- The full four-dimensional reduced tangent action after replacing
`b` by `b - a*v` and `v` by `(alpha, s*alpha + beta)`. The last two
coordinates are the two components of the new lower variation. -/
def segreRulingReducedTangentMatrix (j k f h df dh A dA s : F) : Matrix (Fin 4) (Fin 4) F :=
  !![k * f, df + j * A * f, -j * s * f, j * f;
     k * h, dh + f + j * A * h, -j * s * h, j * h;
     0, f * (dA + A ^ 2), f * (1 - A * s), f * A;
     0, (h + s * f) * (dA + A ^ 2), (h + s * f) * (1 - A * s), (h + s * f) * A]

/-- The actual three-space consists of lower variations proportional
to `(f,g) = (f,h+s*f)`; its scalar is the third input coordinate. -/
def segreRulingThreeSpaceMatrix (f h s : F) : Matrix (Fin 4) (Fin 3) F :=
  !![1, 0, 0; 0, 1, 0; 0, 0, f; 0, 0, h + s * f]

/-- The three-space embedding is faithful wherever the first output
component is generically nonzero. -/
theorem segre_ruling_three_space_injective (f h s : F) (hf : f ≠ 0) :
    Function.Injective (segreRulingThreeSpaceMatrix f h s).toLin' := by
  intro u v huv
  funext i
  fin_cases i
  · simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      segreRulingThreeSpaceMatrix, Fin.sum_univ_succ] using congrFun huv 0
  · simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      segreRulingThreeSpaceMatrix, Fin.sum_univ_succ] using congrFun huv 1
  · apply mul_left_cancel₀ hf
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      segreRulingThreeSpaceMatrix, Fin.sum_univ_succ] using congrFun huv 2

/-- Multiplication constructs both invariance and the exact matrix
(5.2) on that invariant space. -/
theorem segre_ruling_three_space_intertwines (j k f h df dh A dA s : F) :
    segreRulingThreeSpaceMatrix f h s * segreRulingRestrictionMatrix j k f h df dh A dA =
      segreRulingReducedTangentMatrix j k f h df dh A dA s * segreRulingThreeSpaceMatrix f h s := by
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [Matrix.mul_apply, segreRulingThreeSpaceMatrix, segreRulingRestrictionMatrix,
      segreRulingReducedTangentMatrix, Fin.sum_univ_succ] <;> ring

/-- Ambient nilpotence passes to the constructed faithful invariant
three-space, rather than being assumed for equation (5.2). -/
theorem segre_ruling_tangent_reduction_isNilpotent (j k f h df dh A dA s : F) (hf : f ≠ 0)
    (hN : IsNilpotent (segreRulingReducedTangentMatrix j k f h df dh A dA s)) :
    IsNilpotent (segreRulingRestrictionMatrix j k f h df dh A dA) := by
  let M := segreRulingRestrictionMatrix j k f h df dh A dA
  let T := segreRulingReducedTangentMatrix j k f h df dh A dA s
  let i := (segreRulingThreeSpaceMatrix f h s).toLin'
  have hT : IsNilpotent T.toLin' := by
    obtain ⟨n, hn⟩ := hN
    exact ⟨n, by rw [← Matrix.toLin'_pow, hn]; simp⟩
  have hcompat (v : Fin 3 → F) : i (M.toLin' v) = T.toLin' (i v) := by
    change segreRulingThreeSpaceMatrix f h s *ᵥ (M *ᵥ v) = T *ᵥ (segreRulingThreeSpaceMatrix f h s *ᵥ v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      segre_ruling_three_space_intertwines]
  have hM := linear_lift_isNilpotent_of_injective T.toLin' M.toLin' i
    (segre_ruling_three_space_injective f h s hf) hcompat hT
  obtain ⟨n, hn⟩ := hM
  refine ⟨n, ?_⟩
  apply Matrix.toLin'.injective
  simpa only [Matrix.toLin'_pow, map_zero] using hn

/-- The full reduced four-dimensional action already contradicts
nilpotence. Dominance supplies the faithful first component, and the
constructed invariant three-space supplies equation (5.2). -/
theorem dominant_segre_reduced_tangent_lattice_not_nilpotent
    {K : Type*} [Field K] [Algebra K F] [CharZero F]
    (δ : Derivation K F F) (s : F) (hs : δ s = 1)
    (d j : ℕ) (hdegree : 2 * j < d) (f g A : F)
    (hdom : f * δ g - g * δ f ≠ 0) :
    ¬IsNilpotent (segreRulingReducedTangentMatrix (j : F) ((d : F) - (j : F))
      f (g - s * f) (δ f) (δ (g - s * f)) A (δ A) s) := by
  intro hN
  have hf : f ≠ 0 := by
    intro he
    apply hdom
    simp only [he, map_zero, zero_mul, mul_zero, sub_self]
  have hM := segre_ruling_tangent_reduction_isNilpotent _ _ _ _ _ _ _ _ _ hf hN
  exact dominant_segre_ruling_restriction_matrix_not_nilpotent δ s hs d j hdegree f g A hdom hM

end DimensionFourDependence
