import DimensionFourDependence.GaussRulingIncidence
import Mathlib.LinearAlgebra.CrossProduct

/-! # A normalized ternary direction from the actual ruling equations

Two independent ternary covectors have a nonzero cross product. Every
nonzero point annihilated by both is a scalar multiple of that cross
product, also in an ambient coefficient extension. Normalizing a nonzero
coordinate constructs a direction over the original covector field.
-/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 3000000

variable {F G : Type*} [Field F] [Field G]

/-- Dropping a common zero fourth coordinate preserves independence
of the two original four-coordinate covectors. -/
theorem independent_covector_pair_drop_zero_vertex
    (a b : Fin 4 → F) (ha : a (Fin.last 3) = 0) (hb : b (Fin.last 3) = 0)
    (hab : LinearIndependent F ![a, b]) :
    LinearIndependent F ![(fun i : Fin 3 => a i.castSucc), (fun i : Fin 3 => b i.castSucc)] := by
  change a (3 : Fin 4) = 0 at ha
  change b (3 : Fin 4) = 0 at hb
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hfull : ∑ j : Fin 2, c j • (![a, b] : Fin 2 → Fin 4 → F) j = 0 := by
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp [Fin.sum_univ_succ, ha, hb]
    · have he := congrFun hc k
      simpa [Fin.sum_univ_succ] using he
  exact Fintype.linearIndependent_iff.mp hab _ hfull i

/-- A coefficient-field embedding preserves the entire cross product. -/
theorem crossProduct_map_fieldHom (f : F →+* G) (a b : Fin 3 → F) :
    (fun i => f ((a ⨯₃ b) i)) = (fun i => f (a i)) ⨯₃ (fun i => f (b i)) := by
  funext i
  fin_cases i <;> simp [cross_apply]

/-- The actual two ruling equations construct a normalized coefficient-
field direction and its exact common scalar source factor. -/
theorem independent_ternary_covectors_construct_normalized_source_direction
    (f : F →+* G) (a b : Fin 3 → F) (hab : LinearIndependent F ![a, b])
    (z : Fin 3 → G) (hz : z ≠ 0)
    (ha : (fun i => f (a i)) ⬝ᵥ z = 0) (hb : (fun i => f (b i)) ⬝ᵥ z = 0) :
    ∃ (V : Fin 3 → F) (j : Fin 3), V j = 1 ∧ z j ≠ 0 ∧
      (∀ i, z i = f (V i) * z j) ∧ a ⬝ᵥ V = 0 ∧ b ⬝ᵥ V = 0 := by
  let v := a ⨯₃ b
  have hv : v ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr hab
  have hvmap : (fun i => f (v i)) ≠ 0 := by
    intro he
    apply hv
    funext i
    apply f.injective
    simpa only [Pi.zero_apply, map_zero] using congrFun he i
  have hcross : (fun i => f (v i)) ⨯₃ z = 0 := by
    rw [show (fun i => f (v i)) = (fun i => f (a i)) ⨯₃ (fun i => f (b i)) from
      crossProduct_map_fieldHom f a b, cross_cross_eq_smul_sub_smul, ha, hb]
    simp
  have hdep : ¬ LinearIndependent G ![(fun i => f (v i)), z] := by
    rw [← crossProduct_ne_zero_iff_linearIndependent]
    exact fun hn => hn hcross
  obtain ⟨s, hs⟩ : ∃ s : G, s • (fun i => f (v i)) = z := by
    simpa only [LinearIndependent.pair_iff' hvmap, not_forall, not_not] using hdep
  have hs0 : s ≠ 0 := by
    intro he
    exact hz (by rw [← hs, he, zero_smul])
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, v j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hv
  have hfj : f (v j) ≠ 0 := by simpa only [map_zero] using f.injective.ne hj
  have hsource (i : Fin 3) : z i = s * f (v i) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using (congrFun hs i).symm
  refine ⟨fun i => v i / v j, j, div_self hj, ?_, ?_, ?_, ?_⟩
  · rw [hsource]
    exact mul_ne_zero hs0 hfj
  · intro i
    rw [hsource i, hsource j, map_div₀]
    field_simp [hfj] <;> ring
  · simp only [dotProduct, ← mul_div_assoc, ← Finset.sum_div]
    change (a ⬝ᵥ (a ⨯₃ b)) / v j = 0
    rw [dot_self_cross, zero_div]
  · simp only [dotProduct, ← mul_div_assoc, ← Finset.sum_div]
    change (b ⬝ᵥ (a ⨯₃ b)) / v j = 0
    rw [dot_cross_self, zero_div]

end DimensionFourDependence
