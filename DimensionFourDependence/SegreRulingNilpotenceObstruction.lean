import DimensionFourDependence.SegreRulingRestrictionMatrix

/-! # The reduced ruling-preservation matrix cannot be nilpotent -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 3000000

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero F]

/-- Differentiating the exact determinant-forced relation gives the
identity needed in the sum of principal minors. No expression for `A`
or its derivative is supplied. -/
theorem segre_ruling_relation_constructs_derivative_identity
    (δ : Derivation K F F) (f h A : F) (hrel : f + A * h = 0) :
    h ^ 2 * (δ A + A ^ 2) = segreRulingDominanceFactor f h (δ f) (δ h) := by
  have hdiff := congrArg δ hrel
  simp only [map_add, Derivation.leibniz, map_zero, smul_eq_mul] at hdiff
  dsimp only [segreRulingDominanceFactor]
  linear_combination h * hdiff + (A * h - f - δ h) * hrel

/-- Nilpotence forces the determinant relation, its differentiated
identity and a contradictory second trace identity. The only degree
conditions are the two nonzero scalar factors appearing in the paper. -/
theorem segre_ruling_restriction_matrix_not_nilpotent
    (δ : Derivation K F F) (j k f h A : F) (hk : k ≠ 0) (hkj : k - j ≠ 0)
    (hdom : segreRulingDominanceFactor f h (δ f) (δ h) ≠ 0) :
    ¬IsNilpotent (segreRulingRestrictionMatrix j k f h (δ f) (δ h) A (δ A)) := by
  intro hN
  let M := segreRulingRestrictionMatrix j k f h (δ f) (δ h) A (δ A)
  have hdet : M.det = 0 := by
    apply isNilpotent_iff_eq_zero.mp
    obtain ⟨n, hn⟩ := hN
    refine ⟨n, ?_⟩
    change M ^ n = 0 at hn
    rw [← Matrix.det_pow, hn]
    simp
  have hrel : f + A * h = 0 := by
    rw [segre_ruling_restriction_matrix_det] at hdet
    exact (mul_eq_zero.mp hdet).resolve_left (mul_ne_zero hk hdom)
  have hder := segre_ruling_relation_constructs_derivative_identity δ f h A hrel
  have htrace : Matrix.trace M = 0 := (Matrix.isNilpotent_trace_of_isNilpotent hN).eq_zero
  have hN2 : IsNilpotent (M * M) := by
    rw [← pow_two]
    exact hN.pow_of_pos (by decide : (2 : ℕ) ≠ 0)
  have hsquare : Matrix.trace (M * M) = 0 := (Matrix.isNilpotent_trace_of_isNilpotent hN2).eq_zero
  have he := segre_ruling_restriction_matrix_second_trace j k f h (δ f) (δ h) A (δ A)
  change Matrix.trace M ^ 2 - Matrix.trace (M * M) = _ at he
  rw [htrace, hsquare, hrel, mul_zero, add_zero, mul_assoc j (h ^ 2), hder,
    zero_pow (by decide : (2 : ℕ) ≠ 0), sub_self] at he
  have hz : (2 : F) * (k - j) * segreRulingDominanceFactor f h (δ f) (δ h) = 0 := by
    linear_combination -he
  exact (mul_ne_zero (mul_ne_zero (by norm_num) hkj) hdom) hz

/-- The primitive homogeneous part has degree `d - 2*j > 0`, so both
scalar factors needed by the determinant and second-trace argument
are nonzero in characteristic zero. -/
theorem segre_ruling_restriction_matrix_not_nilpotent_of_positive_primitive_degree
    (δ : Derivation K F F) (d j : ℕ) (hdegree : 2 * j < d) (f h A : F)
    (hdom : segreRulingDominanceFactor f h (δ f) (δ h) ≠ 0) :
    ¬IsNilpotent (segreRulingRestrictionMatrix (j : F) ((d : F) - (j : F))
      f h (δ f) (δ h) A (δ A)) := by
  have hk : (d : F) - (j : F) ≠ 0 := by
    rw [← Nat.cast_sub (show j ≤ d by omega)]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hkj : ((d : F) - (j : F)) - (j : F) ≠ 0 := by
    have he : ((d : F) - (j : F)) - (j : F) = ((d - 2 * j : ℕ) : F) := by
      rw [Nat.cast_sub (show 2 * j ≤ d by omega)]
      push_cast
      ring
    rw [he]
    exact Nat.cast_ne_zero.mpr (by omega)
  exact segre_ruling_restriction_matrix_not_nilpotent δ _ _ f h A hk hkj hdom

/-- In the actual normalized ruling chart `h = g - s*f`, dominance
is the nonzero Wronskian `f*g' - g*f'`. This supplies the obstruction
for the exact derivative entries in equation (5.2). -/
theorem dominant_segre_ruling_restriction_matrix_not_nilpotent
    (δ : Derivation K F F) (s : F) (hs : δ s = 1)
    (d j : ℕ) (hdegree : 2 * j < d) (f g A : F)
    (hdom : f * δ g - g * δ f ≠ 0) :
    ¬IsNilpotent (segreRulingRestrictionMatrix (j : F) ((d : F) - (j : F))
      f (g - s * f) (δ f) (δ (g - s * f)) A (δ A)) := by
  apply segre_ruling_restriction_matrix_not_nilpotent_of_positive_primitive_degree δ d j hdegree
  have hh : δ (g - s * f) = δ g - f - s * δ f := by
    simp only [map_sub, Derivation.leibniz, hs, smul_eq_mul, mul_one]
    ring
  rw [hh, segre_ruling_dominance_factor_eq_wronskian]
  exact hdom

end DimensionFourDependence
