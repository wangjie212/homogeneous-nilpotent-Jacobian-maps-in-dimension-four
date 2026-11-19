import DimensionFourDependence.RulingFormCoordinateSpan

/-! # Independent binary ruling forms and their relations survive scalar extension -/

namespace DimensionFourDependence

open Matrix Module

variable {F : Type*} [Field F]

/-- Replacing the first member of an independent pair by a binary
combination with nonzero first coefficient keeps the pair independent. -/
theorem independent_ruling_forms_of_nonzero_binary_coefficient
    {V : Type*} [AddCommGroup V] [Module F V] (s m n : V) (α β : F) (hα : α ≠ 0)
    (hpair : LinearIndependent F ![m, n]) (hlinear : s = α • m + β • n) :
    LinearIndependent F ![s, n] := by
  rw [LinearIndependent.pair_iff] at hpair ⊢
  intro a b hab
  rw [hlinear] at hab
  have he : (a * α) • m + (a * β + b) • n = 0 := by
    simpa only [smul_add, add_smul, mul_smul, add_assoc] using hab
  obtain ⟨ha, hb⟩ := hpair _ _ he
  have ha0 := (mul_eq_zero.mp ha).resolve_right hα
  exact ⟨ha0, by simpa only [ha0, zero_mul, zero_add] using hb⟩

/-- The original linear relation among three covectors is exactly
the corresponding relation among their scalar pairings. -/
theorem ruling_covector_sub_combination_dot {n : ℕ}
    (s m t x : Fin n → F) (α β : F) :
    (fun i => s i - α * m i - β * t i) ⬝ᵥ x =
      s ⬝ᵥ x - α * (m ⬝ᵥ x) - β * (t ⬝ᵥ x) := by
  simp only [dotProduct, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

variable {E : Type*} [Field E] [Algebra F E] {n k : ℕ}

/-- A binary relation among actual ruling-restricted forms gives the
same relation at every point of its scalar-extended matrix kernel. No
ambient covector identity or extended-point relation is assumed. -/
theorem ruling_form_binary_relation_after_extension
    (A : Matrix (Fin k) (Fin n) F) (s m t : Fin n → F) (α β : F)
    (hlinear : rulingFormRestriction (LinearMap.ker A.toLin') s =
      α • rulingFormRestriction (LinearMap.ker A.toLin') m +
        β • rulingFormRestriction (LinearMap.ker A.toLin') t)
    (y : Fin n → E) (hy : A.map (algebraMap F E) *ᵥ y = 0) :
    ((fun i => algebraMap F E (s i)) ⬝ᵥ y) =
      algebraMap F E α * ((fun i => algebraMap F E (m i)) ⬝ᵥ y) +
        algebraMap F E β * ((fun i => algebraMap F E (t i)) ⬝ᵥ y) := by
  let B : Matrix (Fin 1) (Fin n) F := fun _ i => s i - α * m i - β * t i
  have hker : LinearMap.ker A.toLin' ≤ LinearMap.ker B.toLin' := by
    intro x hx
    have hl := LinearMap.congr_fun hlinear ⟨x, hx⟩
    change s ⬝ᵥ x = α * (m ⬝ᵥ x) + β * (t ⬝ᵥ x) at hl
    change B *ᵥ x = 0
    funext r
    change (fun i => s i - α * m i - β * t i) ⬝ᵥ x = 0
    rw [ruling_covector_sub_combination_dot, hl]
    ring
  have hBy := matrix_kernel_le_after_scalar_extension (E := E) A B hker
    (show y ∈ LinearMap.ker (A.map (algebraMap F E)).toLin' from hy)
  have hr := congrFun hBy 0
  change (fun i => algebraMap F E (s i - α * m i - β * t i)) ⬝ᵥ y = 0 at hr
  simp only [map_sub, map_mul] at hr
  rw [ruling_covector_sub_combination_dot] at hr
  linear_combination hr

end DimensionFourDependence
