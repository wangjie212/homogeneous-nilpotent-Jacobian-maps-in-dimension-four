import DimensionFourDependence.ProjectivePrincipalChart
import DimensionFourDependence.ProjectiveChartOverlaps

/-! # Reindexed affine pencil equations under coefficient extension

Coefficient extension commutes with the actual dehomogenization map.
Reindexing an original principal source kernel transports its equation,
and the three nontrivial ratios generate the full projective chart ring.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C E F σ : Type*} [Field C] [Field E] [Field F]

/-- Coefficient extension commutes with actual affine dehomogenization. -/
theorem projectiveDehomogenize_map_coefficients (f : C →+* E)
    (P : MvPolynomial (Option σ) C) :
    projectiveDehomogenize (MvPolynomial.map f P) =
      MvPolynomial.map f (projectiveDehomogenize P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [projectiveDehomogenize]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    cases i <;> simp [map_mul, MvPolynomial.map_X, projectiveDehomogenize_X_none,
      projectiveDehomogenize_X_some, hP]

variable [Algebra C F]

/-- An original principal source kernel is transported by the actual
coordinate reindexing, with the reindexed same equation as generator. -/
theorem reindexed_source_principal_kernel
    (x : Fin 4 → F) (G : MvPolynomial (Fin 4) C)
    (hker : RingHom.ker (aeval x).toRingHom = Ideal.span {G})
    (s : Fin 4 ≃ Option (Fin 3)) :
    RingHom.ker (aeval (fun j => x (s.symm j))).toRingHom = Ideal.span {rename s G} := by
  let e := renameEquiv C s
  have heval : aeval (fun j => x (s.symm j)) = (aeval x).comp e.symm.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, aeval_X]
    change x (s.symm j) = aeval x (rename s.symm (X j))
    simp
  rw [heval]
  change (RingHom.ker (aeval x).toRingHom).comap e.symm.toRingHom = _
  rw [hker]
  change (Ideal.span {G}).comap e.toRingEquiv.symm = _
  rw [Ideal.comap_symm e.toRingEquiv, Ideal.map_span, Set.image_singleton]
  rfl

/-- The three nontrivial original source ratios generate exactly the
same chart as all four ratios, including the coordinate equal to one. -/
theorem projective_three_ratio_algebra_eq_full
    (x : Fin 4 → F) (s : Fin 4 ≃ Option (Fin 3)) (ha : x (s.symm none) ≠ 0) :
    fiberCoordinateAlgebra (L := C) (fun i : Fin 3 => x (s.symm (some i)) / x (s.symm none)) =
      projectiveCoordinateChartAlgebra (C := C) x (s.symm none) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact projectiveCoordinateChartAlgebra_ratio_mem x (s.symm none) (s.symm (some i))
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    dsimp only
    rcases hsi : s i with _ | j
    · have hi : i = s.symm none := by rw [← hsi, s.symm_apply_apply]
      rw [hi, div_self ha]
      exact Subalgebra.one_mem _
    · have hi : i = s.symm (some j) := by rw [← hsi, s.symm_apply_apply]
      rw [hi]
      exact Algebra.subset_adjoin ⟨j, rfl⟩

end DimensionFourDependence
