import DimensionFourDependence.GradedSurjectiveHilbertTransport
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-! # Eliminating the actual infinity hyperplane preserves the graded quotient

Set the original homogenizing coordinate to zero, preserving the
original direction coordinates. The kernel is exactly its principal
coordinate ideal, and the map is onto in every homogeneous degree.
Thus every actual infinity-section Hilbert piece agrees with the
corresponding quotient in the direction-coordinate ring.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F sigma : Type*} [Field F]

/-- The actual homogeneous direction-coordinate projection setting
the original affine homogenizing coordinate to zero. -/
noncomputable def projectiveInfinityCoordinateProjection :
    MvPolynomial (Option sigma) F →ₐ[F] MvPolynomial sigma F :=
  aeval (fun j : Option sigma => j.elim 0 X)

/-- The original infinity coordinate is set to zero. -/
theorem projectiveInfinityCoordinateProjection_none :
    projectiveInfinityCoordinateProjection (F := F) (sigma := sigma) (X none) = 0 := by
  simp [projectiveInfinityCoordinateProjection]

/-- The original direction coordinates retain their labels and values. -/
theorem projectiveInfinityCoordinateProjection_some (i : sigma) :
    projectiveInfinityCoordinateProjection (F := F) (X (some i)) = X i := by
  simp [projectiveInfinityCoordinateProjection]

/-- Inclusion of the original direction polynomial ring is a
specified right inverse of the actual infinity projection. -/
theorem projectiveInfinityCoordinateProjection_rename (P : MvPolynomial sigma F) :
    projectiveInfinityCoordinateProjection (rename some P) = P := by
  have he : (projectiveInfinityCoordinateProjection (F := F) (sigma := sigma)).comp (rename some) =
      AlgHom.id F _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [projectiveInfinityCoordinateProjection]
  exact DFunLike.congr_fun he P

/-- The actual infinity projection preserves every prescribed
homogeneous degree, including when its image is zero. -/
theorem projectiveInfinityCoordinateProjection_homogeneous
    (P : MvPolynomial (Option sigma) F) {d : ℕ} (hP : P.IsHomogeneous d) :
    (projectiveInfinityCoordinateProjection P).IsHomogeneous d := by
  have hvars : ∀ j : Option sigma, (j.elim (0 : MvPolynomial sigma F) X).IsHomogeneous 1 := by
    intro j
    cases j with
    | none => exact isHomogeneous_zero _ _ _
    | some i => exact isHomogeneous_X F i
  simpa only [one_mul, projectiveInfinityCoordinateProjection] using hP.aeval _ hvars

/-- The exact discarded part of every polynomial is an original
multiple of the infinity coordinate. -/
theorem projectiveInfinityCoordinateProjection_remainder_mem
    (P : MvPolynomial (Option sigma) F) :
    P - rename some (projectiveInfinityCoordinateProjection P) ∈
      Ideal.span ({X none} : Set (MvPolynomial (Option sigma) F)) := by
  let I : Ideal (MvPolynomial (Option sigma) F) := Ideal.span {X none}
  induction P using MvPolynomial.induction_on with
  | C a => simp [projectiveInfinityCoordinateProjection]
  | add P Q hP hQ =>
    have he : P + Q - rename some (projectiveInfinityCoordinateProjection (P + Q)) =
        (P - rename some (projectiveInfinityCoordinateProjection P)) +
          (Q - rename some (projectiveInfinityCoordinateProjection Q)) := by
      rw [map_add, map_add]
      ring
    rw [he]
    exact I.add_mem hP hQ
  | mul_X P j hP =>
    cases j with
    | none =>
      simp only [map_mul, projectiveInfinityCoordinateProjection_none, mul_zero, map_zero, sub_zero]
      exact I.mul_mem_left P (Ideal.subset_span (by simp))
    | some i =>
      simp only [map_mul, projectiveInfinityCoordinateProjection_some, rename_X]
      have he : P * X (some i) - rename some (projectiveInfinityCoordinateProjection P) * X (some i) =
          (P - rename some (projectiveInfinityCoordinateProjection P)) * X (some i) := by ring
      rw [he]
      exact I.mul_mem_right (X (some i)) hP

/-- The actual infinity projection has exactly the original
homogenizing coordinate as its full kernel ideal. -/
theorem projectiveInfinityCoordinateProjection_kernel :
    RingHom.ker (projectiveInfinityCoordinateProjection (F := F) (sigma := sigma)).toRingHom =
      Ideal.span ({X none} : Set (MvPolynomial (Option sigma) F)) := by
  apply le_antisymm
  · intro P hP
    have he := projectiveInfinityCoordinateProjection_remainder_mem P
    change projectiveInfinityCoordinateProjection P = 0 at hP
    simpa only [hP, map_zero, sub_zero] using he
  · apply Ideal.span_le.mpr
    rintro _ rfl
    exact projectiveInfinityCoordinateProjection_none

/-- Eliminating the original infinity coordinate preserves every
actual Hilbert quotient piece once that coordinate is an original relation. -/
theorem projectiveHilbertFunction_infinity_coordinate_elimination
    (I : Ideal (MvPolynomial (Option sigma) F)) (hinfinity : X none ∈ I) (d : ℕ) :
    projectiveHilbertFunction I d =
      projectiveHilbertFunction (I.map (projectiveInfinityCoordinateProjection (F := F)).toRingHom) d := by
  let phi : MvPolynomial (Option sigma) F →ₐ[F] MvPolynomial sigma F :=
    projectiveInfinityCoordinateProjection (F := F) (sigma := sigma)
  have hphi : ∀ d P, P.IsHomogeneous d → (phi P).IsHomogeneous d :=
    fun _ P hP => projectiveInfinityCoordinateProjection_homogeneous P hP
  have hsurj : Function.Surjective phi := fun P => ⟨rename some P, projectiveInfinityCoordinateProjection_rename P⟩
  have hpieces : ∀ d, Function.Surjective (homogeneousPolynomialAlgebraMap phi hphi d) := by
    intro d P
    refine ⟨⟨rename some (P : MvPolynomial sigma F), P.property.rename_isHomogeneous⟩, ?_⟩
    apply Subtype.ext
    change projectiveInfinityCoordinateProjection (F := F) (sigma := sigma)
      (rename (some : sigma → Option sigma) (P : MvPolynomial sigma F)) = (P : MvPolynomial sigma F)
    exact projectiveInfinityCoordinateProjection_rename (F := F) (sigma := sigma) (P : MvPolynomial sigma F)
  have hker : RingHom.ker phi.toRingHom ≤ I := by
    change RingHom.ker (projectiveInfinityCoordinateProjection (F := F) (sigma := sigma)).toRingHom ≤ I
    rw [projectiveInfinityCoordinateProjection_kernel]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hinfinity)
  exact projectiveHilbertFunction_surjective_graded_map phi hphi hsurj hpieces I hker d

/-- The image of an original homogeneous ideal under a specified
graded polynomial algebra map is an actual homogeneous ideal. -/
theorem polynomial_graded_image_ideal_isHomogeneous
    {tau : Type*} (phi : MvPolynomial sigma F →ₐ[F] MvPolynomial tau F)
    (hphi : ∀ d P, P.IsHomogeneous d → (phi P).IsHomogeneous d)
    (I : Ideal (MvPolynomial sigma F)) (hI : I.IsHomogeneous (homogeneousSubmodule sigma F)) :
    (I.map phi.toRingHom).IsHomogeneous (homogeneousSubmodule tau F) := by
  let g : homogeneousSubmodule sigma F →+*ᵍ homogeneousSubmodule tau F :=
    { toRingHom := phi.toRingHom, map_mem := fun h => hphi _ _ h }
  let J : HomogeneousIdeal (homogeneousSubmodule sigma F) := ⟨I, hI⟩
  exact (J.map g).isHomogeneous

end DimensionFourDependence
