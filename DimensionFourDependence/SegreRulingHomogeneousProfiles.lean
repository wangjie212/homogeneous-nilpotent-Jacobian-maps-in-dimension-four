import DimensionFourDependence.SegreRulingTangentFrame
import DimensionFourDependence.MatrixNilpotentIntertwiner

/-! # Homogeneous ruling profiles at an arbitrary nonzero radial coordinate -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 3000000

/-- The residue tangent differential in an arbitrary radial chart,
with the actual regular values and coordinate derivatives retained. -/
def segreRulingChartTangentMatrix {R : Type*} [CommRing R]
    (j f g fx fy gx gy a ax ay z s : R) : Matrix (Fin 4) (Fin 4) R :=
  !![fx, fy, -j * s * f, j * f;
     gx, gy, -j * s * g, j * g;
     a * fx + f * ax, a * fy + f * ay,
       a * (-j * s * f) + f * (z - a * s), a * j * f + f * a;
     a * gx + g * ax, a * gy + g * ay,
       a * (-j * s * g) + g * (z - a * s), a * j * g + g * a]

variable {F : Type*} [Field F]

/-- A unit radial coordinate rescales only the two lower variation
coordinates. This is an invertible frame, rather than evaluation of a
rational function at the possibly exceptional value `x = 1`. -/
def segreRulingRadialFrame (x : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, x⁻¹, 0; 0, 0, 0, x⁻¹]

/-- Homogeneity constructs the simultaneous radial frame and the
common nonzero scalar multiplying the raw normalized tangent action. -/
theorem segre_ruling_homogeneous_profiles_intertwine
    (j k f g df dg A dA s x w : F) (hx : x ≠ 0) :
    segreRulingRadialFrame x * (w • segreRulingRawTangentMatrix j k f g df dg A dA s) =
      segreRulingChartTangentMatrix j (x * w * f) (x * w * g)
        (w * (k * f - s * df)) (w * df) (w * (k * g - s * dg)) (w * dg)
        (A / x) ((-A - s * dA) / x ^ 2) (dA / x ^ 2) x⁻¹ s * segreRulingRadialFrame x := by
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [Matrix.mul_apply, segreRulingRadialFrame, segreRulingRawTangentMatrix,
      segreRulingChartTangentMatrix, Fin.sum_univ_succ] <;> field_simp <;> ring

/-- Nilpotence of the actual homogeneous chart action forces nilpotence
of the normalized raw action. No specialization of the radial coordinate
or nilpotence of a preselected three-by-three matrix is assumed. -/
theorem segre_ruling_homogeneous_chart_isNilpotent_raw
    (j k f g df dg A dA s x w : F) (hx : x ≠ 0) (hw : w ≠ 0)
    (hN : IsNilpotent (segreRulingChartTangentMatrix j (x * w * f) (x * w * g)
      (w * (k * f - s * df)) (w * df) (w * (k * g - s * dg)) (w * dg)
      (A / x) ((-A - s * dA) / x ^ 2) (dA / x ^ 2) x⁻¹ s)) :
    IsNilpotent (segreRulingRawTangentMatrix j k f g df dg A dA s) := by
  let Q : Matrix (Fin 4) (Fin 4) F := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, x, 0; 0, 0, 0, x]
  have hQP : Q * segreRulingRadialFrame x = 1 := by
    ext i l
    fin_cases i <;> fin_cases l <;> simp [Q, segreRulingRadialFrame, Matrix.mul_apply, Fin.sum_univ_succ, hx]
  have hi : Function.Injective (segreRulingRadialFrame x).toLin' := by
    have hleft : Function.LeftInverse (fun v => Q *ᵥ v) (segreRulingRadialFrame x).toLin' := by
      intro v
      change Q *ᵥ (segreRulingRadialFrame x *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
    exact hleft.injective
  have hscaled := matrix_isNilpotent_of_injective_intertwiner _ _ (segreRulingRadialFrame x) hi
    (segre_ruling_homogeneous_profiles_intertwine j k f g df dg A dA s x w hx) hN
  simpa only [smul_smul, inv_mul_cancel₀ hw, one_smul] using hscaled.smul w⁻¹

/-- The differential contradiction of Lemma 5.2 is valid at the actual
generic nonzero radial coordinate. Homogeneous profiles and dominance
supply all reduced matrices, invariant spaces and nonzero degree factors. -/
theorem dominant_segre_homogeneous_chart_not_nilpotent
    {K : Type*} [Field K] [Algebra K F] [CharZero F]
    (δ : Derivation K F F) (s : F) (hs : δ s = 1)
    (d j : ℕ) (hdegree : 2 * j < d) (f g A x w : F) (hx : x ≠ 0) (hw : w ≠ 0)
    (hdom : f * δ g - g * δ f ≠ 0) :
    ¬IsNilpotent (segreRulingChartTangentMatrix (j : F) (x * w * f) (x * w * g)
      (w * (((d : F) - (j : F)) * f - s * δ f)) (w * δ f)
      (w * (((d : F) - (j : F)) * g - s * δ g)) (w * δ g)
      (A / x) ((-A - s * δ A) / x ^ 2) (δ A / x ^ 2) x⁻¹ s) := by
  intro hN
  exact dominant_segre_raw_tangent_matrix_not_nilpotent δ s hs d j hdegree f g A hdom
    (segre_ruling_homogeneous_chart_isNilpotent_raw _ _ _ _ _ _ _ _ _ _ _ hx hw hN)

end DimensionFourDependence
