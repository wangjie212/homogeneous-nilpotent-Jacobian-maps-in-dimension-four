import DimensionFourDependence.MatrixRankFieldMap

/-! # A one-dimensional matrix kernel descends through field extension

A rank-three four-by-four matrix has a one-dimensional kernel before and
after any field extension. A nonzero original-field kernel vector stays
nonzero and spans the extended kernel. Thus every nonzero extended
solution is a scalar multiple of a vector over the original field.
-/

namespace DimensionFourDependence

open Matrix Module

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- A rank-three square matrix in four coordinates has a one-dimensional kernel. -/
theorem rank_three_matrix_kernel_finrank
    (A : Matrix (Fin 4) (Fin 4) F) (hA : A.rank = 3) :
    finrank F (LinearMap.ker A.toLin') = 1 := by
  have hd := LinearMap.finrank_range_add_finrank_ker A.toLin'
  have hr : finrank F (LinearMap.range A.toLin') = 3 := hA
  simp only [Module.finrank_pi, Fintype.card_fin] at hd
  omega

/-- A nonzero solution after field extension is a nonzero scalar
multiple of an actual nonzero original-field kernel vector. -/
theorem rank_three_kernel_vector_after_extension
    (A : Matrix (Fin 4) (Fin 4) F) (hA : A.rank = 3)
    (O : Fin 4 → E) (hO : O ≠ 0)
    (hAO : A.map (algebraMap F E) *ᵥ O = 0) :
    ∃ v : Fin 4 → F, v ≠ 0 ∧ A *ᵥ v = 0 ∧
      ∃ t : E, t ≠ 0 ∧ O = t • (fun i => algebraMap F E (v i)) := by
  have hk := rank_three_matrix_kernel_finrank A hA
  obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero
    (R := F) (M := LinearMap.ker A.toLin')).mp (show 0 < finrank F (LinearMap.ker A.toLin') by omega)
  have hv0 : (v : Fin 4 → F) ≠ 0 := fun hz => hv (Subtype.ext hz)
  let w : Fin 4 → E := fun i => algebraMap F E ((v : Fin 4 → F) i)
  have hw0 : w ≠ 0 := by
    intro hz
    apply hv0
    funext i
    apply (algebraMap F E).injective
    simpa only [w, map_zero, Pi.zero_apply] using congrFun hz i
  have hAw : A.map (algebraMap F E) *ᵥ w = 0 := by
    funext i
    have hi := congrArg (algebraMap F E) (congrFun v.property i)
    simp only [Pi.zero_apply, map_zero] at hi
    change algebraMap F E ((A *ᵥ (v : Fin 4 → F)) i) = 0 at hi
    simpa [w, Matrix.mulVec, dotProduct, map_sum, map_mul] using hi
  have hrE : (A.map (algebraMap F E)).rank = 3 := by rw [matrix_rank_field_map, hA]
  have hkE := rank_three_matrix_kernel_finrank (A.map (algebraMap F E)) hrE
  let vE : LinearMap.ker (A.map (algebraMap F E)).toLin' := ⟨w, hAw⟩
  have hvE : vE ≠ 0 := fun hz => hw0 (congrArg Subtype.val hz)
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' vE hvE).mp hkE ⟨O, hAO⟩
  have he : t • w = O := congrArg Subtype.val ht
  refine ⟨v, hv0, v.property, t, ?_, he.symm⟩
  intro ht0
  apply hO
  rw [← he, ht0, zero_smul]

end DimensionFourDependence
