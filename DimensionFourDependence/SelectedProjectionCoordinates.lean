import DimensionFourDependence.ReindexedProjectionFieldGenerator
import DimensionFourDependence.ResidueProjectionActionCompatibility

/-! # The projection coordinate order selected by an actual divisor

The first base variable is the outer projection coordinate; the second
is the divisor's chosen residue parameter. Renaming only these two base
variables preserves the entire equation, its total degree and full
fiber degree.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k A L : Type*} [Field k] [CommRing A] [Algebra k A]
  [CommRing L] [Algebra k L]

/-- The original three affine projection coordinates with their fiber
slot distinguished, in the same order as the constructed equation. -/
noncomputable def linearProjectionOptionCoordinate
    (T : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k)) (c : Fin 3 → A) : Option (Fin 2) → A :=
  fun i => linearProjectionCoordinate T c ((finSuccEquiv' (0 : Fin 3)).symm i)

/-- Applying an original constant-compatible algebra map to the
projection is the same as projecting the original mapped coordinates. -/
theorem linearProjectionCoordinate_algHom
    (T : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k)) (c : Fin 3 → A) (φ : A →ₐ[k] L) (i : Fin 3) :
    φ (linearProjectionCoordinate T c i) = linearProjectionCoordinate T (fun j => φ (c j)) i := by
  change φ (aeval c ((linearPolynomialCoordinateEquiv T).symm (X i))) =
    aeval (fun j => φ (c j)) ((linearPolynomialCoordinateEquiv T).symm (X i))
  have hev : φ.comp (aeval c) = aeval (fun j => φ (c j)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp
  exact AlgHom.congr_fun hev _

/-- A base-coordinate permutation acts on the original three coordinate
indices and leaves the original fiber coordinate in place. -/
noncomputable def projectionCoordinateBaseReindex (ρ : Fin 2 ≃ Fin 2) : Fin 3 ≃ Fin 3 :=
  (finSuccEquiv' (0 : Fin 3)).trans
    ((Equiv.optionCongr ρ).trans (finSuccEquiv' (0 : Fin 3)).symm)

/-- The reindexed original affine coordinates agree with the original
distinguished-fiber projection after reordering only the two base slots. -/
theorem projectionCoordinateBaseReindex_coordinate
    (T : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k)) (c : Fin 3 → A)
    (ρ : Fin 2 ≃ Fin 2) (i : Fin 3) :
    linearProjectionCoordinate T c (projectionCoordinateBaseReindex ρ i) =
      linearProjectionOptionCoordinate T c (Equiv.optionCongr ρ (finSuccEquiv' (0 : Fin 3) i)) := rfl

/-- Renaming the actual two base variables preserves nonvanishing,
total degree, full fiber degree and every original coordinate relation. -/
theorem projection_base_reindexed_equation
    (y : Option (Fin 2) → A) (ρ : Fin 2 ≃ Fin 2)
    (g : MvPolynomial (Option (Fin 2)) k) (hg : g ≠ 0)
    (hfull : g.degreeOf none = g.totalDegree) (hroot : aeval y g = 0) :
    let g' := renameEquiv k (Equiv.optionCongr ρ).symm g
    g' ≠ 0 ∧ g'.totalDegree = g.totalDegree ∧ g'.degreeOf none = g'.totalDegree ∧
      aeval (fun i => y (Equiv.optionCongr ρ i)) g' = 0 := by
  let g' := renameEquiv k (Equiv.optionCongr ρ).symm g
  have hn : g' ≠ 0 := by
    intro hz
    exact hg ((renameEquiv k (Equiv.optionCongr ρ).symm).injective
      (hz.trans (map_zero _).symm))
  have hd : g'.totalDegree = g.totalDegree := totalDegree_renameEquiv _ g
  have hf : g'.degreeOf none = g.degreeOf none := by
    have h := degreeOf_rename_of_injective (p := g) (Equiv.optionCongr ρ).symm.injective none
    change g'.degreeOf none = g.degreeOf none at h
    exact h
  refine ⟨hn, hd, hf.trans (hfull.trans hd.symm), ?_⟩
  change aeval (fun i => y (Equiv.optionCongr ρ i)) (rename (Equiv.optionCongr ρ).symm g) = 0
  rw [aeval_rename]
  have hvalues : (fun i => y (Equiv.optionCongr ρ i)) ∘ (Equiv.optionCongr ρ).symm = y := by
    funext i
    change y (Equiv.optionCongr ρ ((Equiv.optionCongr ρ).symm i)) = y i
    rw [Equiv.apply_symm_apply]
  rw [hvalues]
  exact hroot

end DimensionFourDependence
