import DimensionFourDependence.LinearProjectionCoordinateChange

/-! # Monic projection coordinates constructed on the original affine surface

The original generators and a nonzero equation supply actual new
generators and an actual transformed equation. The equation stays nonzero,
retains the exact original total degree, has full degree in the fiber
coordinate, and vanishes on the constructed generators.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k A : Type*} [Field k] [Infinite k] [CommRing A] [Algebra k A] {n : ℕ}

/-- Original affine generators and a nonzero relation construct an
invertible linear projection coordinate system. The fiber variable has
the full original degree, the original affine algebra is still generated,
and its actual relation is preserved. No monic direction is assumed. -/
theorem exists_actual_monic_projection_coordinates
    (x : Fin (n + 1) → A) (hx : Algebra.adjoin k (Set.range x) = ⊤)
    (f : MvPolynomial (Fin (n + 1)) k) (hf : f ≠ 0) (hroot : aeval x f = 0) :
    ∃ T : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k),
      let r := finSuccEquiv' (0 : Fin (n + 1))
      let y := fun i : Option (Fin n) => linearProjectionCoordinate T x (r.symm i)
      let g := renameEquiv k r
        (linearPolynomialPullback (LinearMap.toMatrix' T.toLinearMap) f)
      Algebra.adjoin k (Set.range y) = ⊤ ∧ g ≠ 0 ∧ g.totalDegree = f.totalDegree ∧
        g.degreeOf none = g.totalDegree ∧ aeval y g = 0 := by
  classical
  obtain ⟨T, hnonzero, hdegree, hfull⟩ := exists_linear_monic_projection_coordinates f hf
  let r := finSuccEquiv' (0 : Fin (n + 1))
  let y := fun i : Option (Fin n) => linearProjectionCoordinate T x (r.symm i)
  let g₀ := linearPolynomialPullback (LinearMap.toMatrix' T.toLinearMap) f
  let g := renameEquiv k r g₀
  have hyrange : Set.range y = Set.range (linearProjectionCoordinate T x) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨r.symm i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨r i, by simp [y]⟩
  have hy : Algebra.adjoin k (Set.range y) = ⊤ := by
    rw [hyrange]
    exact linearProjectionCoordinate_adjoin_eq_top T x hx
  have hg : g ≠ 0 := by
    intro hzero
    apply hnonzero
    apply (renameEquiv k r).injective
    simpa only [map_zero] using hzero
  have hgdegree : g.totalDegree = f.totalDegree :=
    (totalDegree_renameEquiv r g₀).trans hdegree
  have hgfiber : g.degreeOf none = g₀.degreeOf 0 := by
    change (rename r g₀).degreeOf none = g₀.degreeOf 0
    have h := degreeOf_rename_of_injective (p := g₀) r.injective (0 : Fin (n + 1))
    simpa only [r, finSuccEquiv'_at] using h
  have hgfull : g.degreeOf none = g.totalDegree :=
    hgfiber.trans (hfull.trans (totalDegree_renameEquiv r g₀).symm)
  have hgroot : aeval y g = 0 := by
    change aeval y (rename r g₀) = 0
    rw [aeval_rename]
    have hcoords : y ∘ r = linearProjectionCoordinate T x := by
      funext i
      simp [y]
    rw [hcoords]
    exact (linearProjectionCoordinate_eval_transformed T x f).trans hroot
  exact ⟨T, hy, hg, hgdegree, hgfull, hgroot⟩

end DimensionFourDependence
