import DimensionFourDependence.SegreRulingTangentReduction

/-! # The two tangent-coordinate changes that construct the Segre reduced matrix -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 3000000

variable {F : Type*} [Field F]

/-- The homogeneous ruling-chart differential before either change of
variation coordinates. The upper rows are the derivative of `F`; the
lower rows are `A*upper + F*(b1 + A*(b2-s*b1) + a_x*v1 + a_y*v2)`,
with the Euler-derived entries `a_x = -A-s*A'`, `a_y = A'`. -/
def segreRulingRawTangentMatrix (j k f g df dg A dA s : F) : Matrix (Fin 4) (Fin 4) F :=
  !![k * f - s * df, df, -j * s * f, j * f;
     k * g - s * dg, dg, -j * s * g, j * g;
     A * (k * f - s * df) + f * (-A - s * dA), A * df + f * dA,
       A * (-j * s * f) + f * (1 - A * s), A * j * f + f * A;
     A * (k * g - s * dg) + g * (-A - s * dA), A * dg + g * dA,
       A * (-j * s * g) + g * (1 - A * s), A * j * g + g * A]

/-- Input coordinates `v=(alpha,s*alpha+beta)`, `b=b'+A*v`. The same
change is used for input and output, as required to preserve nilpotence. -/
def segreRulingTangentFrame (A s : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; s, 1, 0, 0; A, 0, 1, 0; A * s, A, 0, 1]

/-- The inverse sends `(v,b)` to `(v1,v2-s*v1,b1-A*v1,b2-A*v2)`. -/
def segreRulingTangentFrameInverse (A s : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; -s, 1, 0, 0; -A, 0, 1, 0; 0, -A, 0, 1]

/-- The frame change is invertible with this explicit inverse. -/
theorem segre_ruling_tangent_frame_inverse (A s : F) :
    segreRulingTangentFrameInverse A s * segreRulingTangentFrame A s = 1 := by
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [Matrix.mul_apply, segreRulingTangentFrame, segreRulingTangentFrameInverse,
      Fin.sum_univ_succ, Matrix.one_apply] <;> ring

/-- The original four-dimensional differential constructs the exact
reduced tangent matrix through a single simultaneous change of frame. -/
theorem segre_ruling_tangent_frame_intertwines (j k f g df dg A dA s : F) :
    segreRulingTangentFrame A s *
        segreRulingReducedTangentMatrix j k f (g - s * f) df (dg - f - s * df) A dA s =
      segreRulingRawTangentMatrix j k f g df dg A dA s * segreRulingTangentFrame A s := by
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [Matrix.mul_apply, segreRulingTangentFrame, segreRulingReducedTangentMatrix,
      segreRulingRawTangentMatrix, Fin.sum_univ_succ] <;> ring

/-- Nilpotence of the raw tangent reduction gives nilpotence of the
constructed normalized reduction, using the explicitly invertible frame. -/
theorem segre_ruling_raw_tangent_isNilpotent_reduction (j k f g df dg A dA s : F)
    (hN : IsNilpotent (segreRulingRawTangentMatrix j k f g df dg A dA s)) :
    IsNilpotent (segreRulingReducedTangentMatrix j k f (g - s * f)
      df (dg - f - s * df) A dA s) := by
  let T := segreRulingRawTangentMatrix j k f g df dg A dA s
  let M := segreRulingReducedTangentMatrix j k f (g - s * f) df (dg - f - s * df) A dA s
  let i := (segreRulingTangentFrame A s).toLin'
  have hi : Function.Injective i := by
    have hleft : Function.LeftInverse (fun v => segreRulingTangentFrameInverse A s *ᵥ v) i := by
      intro v
      change segreRulingTangentFrameInverse A s *ᵥ (segreRulingTangentFrame A s *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, segre_ruling_tangent_frame_inverse, Matrix.one_mulVec]
    exact hleft.injective
  have hT : IsNilpotent T.toLin' := by
    obtain ⟨n, hn⟩ := hN
    exact ⟨n, by rw [← Matrix.toLin'_pow, hn]; simp⟩
  have hcompat (v : Fin 4 → F) : i (M.toLin' v) = T.toLin' (i v) := by
    change segreRulingTangentFrame A s *ᵥ (M *ᵥ v) = T *ᵥ (segreRulingTangentFrame A s *ᵥ v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, segre_ruling_tangent_frame_intertwines]
  obtain ⟨n, hn⟩ := linear_lift_isNilpotent_of_injective T.toLin' M.toLin' i hi hcompat hT
  refine ⟨n, ?_⟩
  apply Matrix.toLin'.injective
  simpa only [Matrix.toLin'_pow, map_zero] using hn

/-- Dominance and positive primitive degree already exclude nilpotence
of the raw ruling-chart differential, with both frame changes and the
invariant three-space constructed internally. -/
theorem dominant_segre_raw_tangent_matrix_not_nilpotent
    {K : Type*} [Field K] [Algebra K F] [CharZero F]
    (δ : Derivation K F F) (s : F) (hs : δ s = 1)
    (d j : ℕ) (hdegree : 2 * j < d) (f g A : F)
    (hdom : f * δ g - g * δ f ≠ 0) :
    ¬IsNilpotent (segreRulingRawTangentMatrix (j : F) ((d : F) - (j : F))
      f g (δ f) (δ g) A (δ A) s) := by
  intro hN
  have hred := segre_ruling_raw_tangent_isNilpotent_reduction _ _ _ _ _ _ _ _ _ hN
  have hh : δ (g - s * f) = δ g - f - s * δ f := by
    simp only [map_sub, Derivation.leibniz, hs, smul_eq_mul, mul_one]
    ring
  rw [← hh] at hred
  exact dominant_segre_reduced_tangent_lattice_not_nilpotent δ s hs d j hdegree f g A hdom hred

end DimensionFourDependence
