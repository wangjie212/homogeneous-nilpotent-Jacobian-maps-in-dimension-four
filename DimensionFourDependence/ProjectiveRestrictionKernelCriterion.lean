import DimensionFourDependence.Lemma43ProjectiveRestriction

/-! # The cone substitution kernel characterizes actual projective dominance -/

namespace DimensionFourDependence

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Equality of the actual polynomial relation primes gives equality
of the actual projective image closures. -/
theorem projective_image_eq_of_relation_ideal_eq
    (A B : Fin 4 → MvPolynomial (Fin 4) K) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hA : IsHomogMap A a) (hB : IsHomogMap B b)
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (he : imageRelationIdeal A = imageRelationIdeal B) :
    projectiveImageSet A ha hA hA0 = projectiveImageSet B hb hB hB0 := by
  have hp : projectiveImageGenericPoint A ha hA hA0 = projectiveImageGenericPoint B hb hB hB0 := by
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.toIdeal_injective
    exact he
  unfold projectiveImageSet
  rw [hp]

/-- The exact cone substitution kernel suffices for dominance in
Mathlib's projective spectrum; this is the converse of the original
projective dominance-to-kernel construction. -/
theorem original_projective_restriction_dominant_of_cone_kernel
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hH0 : H ≠ 0) (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (P : Fin 4 → MvPolynomial (Fin 4) K) {m : ℕ} (hm : 0 < m)
    (hP : IsHomogMap P m) (hprim : IsPrimitiveVec P)
    (hkernel : ∀ z, aeval P z ∈ imageRelationIdeal H ↔ z ∈ imageRelationIdeal H) :
    originalProjectiveRestrictionDominant H hd hH hH0 hrank I P hm hP hprim := by
  apply projective_image_eq_of_relation_ideal_eq (fun i => aeval H (P i)) H
    (Nat.mul_pos hd hm) hd (fun i => (hP i).aeval H hH) hH
    (primitive_part_composite_image_ne_zero H hrank I P hprim) hH0
  apply Ideal.ext
  intro z
  change aeval (fun i => aeval H (P i)) z = 0 ↔ z ∈ imageRelationIdeal H
  rw [← comp_aeval_apply P (aeval H) z]
  exact hkernel z

end DimensionFourDependence
