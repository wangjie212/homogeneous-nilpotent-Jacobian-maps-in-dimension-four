import DimensionFourDependence.RulingFormCoordinateSpan

/-! # A constant kernel of dimension at most one stays a single constant line after extension -/

namespace DimensionFourDependence

open Matrix Module

variable {K E : Type*} [Field K] [Field E] [Algebra K E] {m n : ℕ}

/-- A matrix kernel of dimension at most one has an original-field
generator for every scalar-extended solution. The generator may be zero
when the original kernel is zero. No extended kernel dimension is assumed. -/
theorem matrix_kernel_finrank_le_one_constant_generator
    (A : Matrix (Fin m) (Fin n) K) (hdim : finrank K (LinearMap.ker A.toLin') ≤ 1) :
    ∃ c : Fin n → K, A *ᵥ c = 0 ∧ ∀ x : Fin n → E,
      A.map (algebraMap K E) *ᵥ x = 0 → ∃ t : E, x = t • (fun i => algebraMap K E (c i)) := by
  classical
  by_cases hker : LinearMap.ker A.toLin' = ⊥
  · refine ⟨0, Matrix.mulVec_zero _, fun x hx => ⟨0, ?_⟩⟩
    have hsource : ∀ z ∈ LinearMap.ker A.toLin', ∀ i,
        z i = (0 : K) * ((0 : Fin n → K) ⬝ᵥ z) + 0 * ((0 : Fin n → K) ⬝ᵥ z) := by
      intro z hz i
      have hz0 : z = 0 := by simpa only [hker, Submodule.mem_bot] using hz
      simp only [hz0, Pi.zero_apply, zero_mul, add_zero]
    have hcoord := matrix_kernel_coordinate_form_span_after_extension A 0 0 0 0 hsource x hx
    funext i
    simpa only [map_zero, zero_mul, add_zero, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] using hcoord i
  · obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).mp hker
    have hpos : 0 < finrank K (LinearMap.ker A.toLin') := by
      by_contra! hn
      exact hker (Submodule.finrank_eq_zero.mp (by omega))
    have hdim1 : finrank K (LinearMap.ker A.toLin') = 1 := by omega
    let cW : LinearMap.ker A.toLin' := ⟨c, hc⟩
    have hcW : cW ≠ 0 := fun h => hc0 (congrArg Subtype.val h)
    obtain ⟨p, hp⟩ : ∃ p, c p ≠ 0 := by
      simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hc0
    have hsource : ∀ z ∈ LinearMap.ker A.toLin', ∀ i,
        z i = (c i / c p) * ((Pi.single p 1 : Fin n → K) ⬝ᵥ z) +
          0 * ((0 : Fin n → K) ⬝ᵥ z) := by
      intro z hz i
      obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' cW hcW).mp hdim1 ⟨z, hz⟩
      have ht' : t • c = z := congrArg Subtype.val ht
      have hdot : (Pi.single p 1 : Fin n → K) ⬝ᵥ z = z p := by simp [dotProduct, Pi.single_apply]
      rw [hdot, ← ht']
      simp only [Pi.smul_apply, smul_eq_mul, zero_mul, add_zero]
      field_simp
    refine ⟨c, hc, fun x hx => ?_⟩
    have hcoord := matrix_kernel_coordinate_form_span_after_extension A (Pi.single p 1) 0
      (fun i => c i / c p) 0 hsource x hx
    have hcoord' (i : Fin n) : x i = algebraMap K E (c i / c p) * x p := by
      simpa [dotProduct, Pi.single_apply] using hcoord i
    refine ⟨x p / algebraMap K E (c p), ?_⟩
    funext i
    rw [hcoord' i]
    simp only [map_div₀, Pi.smul_apply, smul_eq_mul]
    ring

/-- A nonzero extended solution of a kernel of dimension at most
one is a nonzero scalar multiple of an original nonzero kernel vector. -/
theorem small_matrix_kernel_nonzero_vector_descends
    (A : Matrix (Fin m) (Fin n) K) (hdim : finrank K (LinearMap.ker A.toLin') ≤ 1)
    (x : Fin n → E) (hx : x ≠ 0) (hAx : A.map (algebraMap K E) *ᵥ x = 0) :
    ∃ c : Fin n → K, c ≠ 0 ∧ A *ᵥ c = 0 ∧
      ∃ t : E, t ≠ 0 ∧ x = t • (fun i => algebraMap K E (c i)) := by
  obtain ⟨c, hc, hgen⟩ := matrix_kernel_finrank_le_one_constant_generator (E := E) A hdim
  obtain ⟨t, ht⟩ := hgen x hAx
  have hc0 : c ≠ 0 := by
    intro hzero
    apply hx
    funext i
    simpa only [hzero, Pi.zero_apply, map_zero, Pi.smul_apply, smul_eq_mul, mul_zero] using congrFun ht i
  have ht0 : t ≠ 0 := by
    intro hzero
    apply hx
    simpa only [hzero, zero_smul] using ht
  exact ⟨c, hc0, hc, t, ht0, ht⟩

/-- Every projective ratio of a nonzero scalar-extended point in
such a kernel is an original-field constant, in any nonzero frame. -/
theorem small_matrix_kernel_projective_ratios_descend
    (A : Matrix (Fin m) (Fin n) K) (hdim : finrank K (LinearMap.ker A.toLin') ≤ 1)
    (x : Fin n → E) (hAx : A.map (algebraMap K E) *ᵥ x = 0) (a : Fin n) (ha : x a ≠ 0) :
    ∃ b : Fin n → K, b a = 1 ∧ ∀ i, x i / x a = algebraMap K E (b i) := by
  have hx : x ≠ 0 := fun h => ha (congrFun h a)
  obtain ⟨c, _hc0, _hc, t, ht0, ht⟩ := small_matrix_kernel_nonzero_vector_descends A hdim x hx hAx
  have hca : c a ≠ 0 := by
    intro hzero
    apply ha
    rw [ht]
    simp only [Pi.smul_apply, smul_eq_mul, hzero, map_zero, mul_zero]
  have hcaE : algebraMap K E (c a) ≠ 0 := by
    simpa only [map_zero] using (algebraMap K E).injective.ne hca
  refine ⟨fun i => c i / c a, div_self hca, fun i => ?_⟩
  rw [ht]
  simp only [Pi.smul_apply, smul_eq_mul, map_div₀]
  field_simp

end DimensionFourDependence
