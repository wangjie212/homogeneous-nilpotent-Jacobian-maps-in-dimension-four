import DimensionFourDependence.Defs

/-! # Actual localization subalgebras inside a field

Adjoining the actual inverse of a nonzero denominator gives the localization
away from that denominator. All maps are the original field inclusions.
-/

namespace DimensionFourDependence

variable {A F : Type*} [CommRing A] [Field F] [Algebra A F] [FaithfulSMul A F]

/-- The localization realized as the actual inverse-adjoining subalgebra
of the ambient field. -/
noncomputable def adjoinInverseAlgebra (r : A) : Subalgebra A F :=
  Algebra.adjoin A {(algebraMap A F r)⁻¹}

omit [FaithfulSMul A F] in
/-- Every inverse-adjoining expression has an actual common denominator. -/
theorem adjoinInverseAlgebra_clear_denominator (r : A)
    (hr : algebraMap A F r ≠ 0) (x : F) (hx : x ∈ adjoinInverseAlgebra (F := F) r) :
    ∃ (n : ℕ) (a : A), x * algebraMap A F r ^ n = algebraMap A F a := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨1, 1, by simp [hr]⟩
  | algebraMap a => exact ⟨0, a, by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨n, a, ha⟩ := ihx
    obtain ⟨m, b, hb⟩ := ihy
    refine ⟨n + m, a * r ^ m + b * r ^ n, ?_⟩
    simp only [map_add, map_mul, map_pow]
    calc
      _ = (x * algebraMap A F r ^ n) * algebraMap A F r ^ m +
          (y * algebraMap A F r ^ m) * algebraMap A F r ^ n := by rw [pow_add]; ring
      _ = _ := by rw [ha, hb]
  | mul x y hx hy ihx ihy =>
    obtain ⟨n, a, ha⟩ := ihx
    obtain ⟨m, b, hb⟩ := ihy
    refine ⟨n + m, a * b, ?_⟩
    rw [map_mul, pow_add]
    calc
      _ = (x * algebraMap A F r ^ n) * (y * algebraMap A F r ^ m) := by ring
      _ = _ := by rw [ha, hb]

/-- The actual inverse-adjoining subalgebra is the actual denominator
localization, with its inherited field inclusion. -/
theorem adjoinInverseAlgebra_isLocalization (r : A) (hr : algebraMap A F r ≠ 0) :
    IsLocalization.Away r (adjoinInverseAlgebra (F := F) r) := by
  let T := adjoinInverseAlgebra (F := F) r
  apply IsLocalization.Away.mk r
  · apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨(algebraMap A F r)⁻¹, Algebra.subset_adjoin rfl⟩, ?_⟩
    apply Subtype.ext
    exact mul_inv_cancel₀ hr
  · intro x
    obtain ⟨n, a, ha⟩ := adjoinInverseAlgebra_clear_denominator r hr x.val x.property
    exact ⟨n, a, Subtype.ext ha⟩
  · intro a b hab
    have he : algebraMap A F a = algebraMap A F b := congrArg Subtype.val hab
    have heq := (FaithfulSMul.algebraMap_injective A F) he
    exact ⟨0, by simpa only [pow_zero, one_mul] using heq⟩

end DimensionFourDependence
