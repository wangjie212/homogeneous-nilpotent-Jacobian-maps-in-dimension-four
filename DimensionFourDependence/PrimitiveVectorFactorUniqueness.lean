import DimensionFourDependence.QuasiTranslationFiberDivisorTangency

/-! # Primitive output presentations differ by an actual polynomial unit -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K] {n : ℕ}
local notation "R₀" => MvPolynomial (Fin n) K

/-- Two primitive polynomial-vector presentations of the same map
differ by an actual polynomial unit. Common-factor cancellation is
proved in the original source ring, without choosing parameters. -/
theorem primitive_vector_common_factor_presentations_construct_unit_ratio
    (A B : Fin n → R₀) (hA : IsPrimitiveVec A) (hB : IsPrimitiveVec B)
    (g h : R₀) (hh : h ≠ 0) (hrep : ∀ i, g * A i = h * B i) :
    ∃ r : R₀, IsUnit r ∧ ∀ i, B i = r * A i := by
  have hdiv : h ∣ g := primitive_vector_cancels_common_scalar_divisibility A hA h g
    (fun i => ⟨B i, hrep i⟩)
  obtain ⟨r, hr⟩ := hdiv
  have hBrep (i) : B i = r * A i := by
    apply mul_left_cancel₀ hh
    rw [← hrep i, hr, mul_assoc]
  exact ⟨r, hB r (fun i => ⟨A i, hBrep i⟩), hBrep⟩

/-- Every prime containing one primitive output presentation contains
the other. This compares the actual intrinsic primitive base without
identifying two separately chosen source-pencil parameters. -/
theorem primitive_vector_common_factor_presentations_prime_membership_iff
    (A B : Fin n → R₀) (hA : IsPrimitiveVec A) (hB : IsPrimitiveVec B)
    (g h : R₀) (hh : h ≠ 0) (hrep : ∀ i, g * A i = h * B i)
    (Q : Ideal R₀) [Q.IsPrime] :
    (∀ i, A i ∈ Q) ↔ ∀ i, B i ∈ Q := by
  obtain ⟨r, hr, hBr⟩ := primitive_vector_common_factor_presentations_construct_unit_ratio A B hA hB g h hh hrep
  constructor
  · intro h i
    rw [hBr i]
    exact Q.mul_mem_left r (h i)
  · intro h i
    have hm := h i
    rw [hBr i] at hm
    exact ((inferInstance : Q.IsPrime).mem_or_mem hm).resolve_left
      (fun he => (inferInstance : Q.IsPrime).ne_top (Q.eq_top_of_isUnit_mem he hr))

end DimensionFourDependence
