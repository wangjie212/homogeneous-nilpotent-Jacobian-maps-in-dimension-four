import DimensionFourDependence.ProjectivePullbackHyperplaneSheaf
import DimensionFourDependence.PolynomialProjectiveProperties
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # The affine nonvanishing cover of the projective hyperplane bundle -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 750000
set_option synthInstance.maxHeartbeats 60000
set_option quotPrecheck false

variable {k : Type u} [Field k]
local notation "G" => homogeneousSubmodule (Fin 4) k
local notation "P₃" => Proj G
local notation "U" a:max => Proj.basicOpen G (X a)

/-- The nonvanishing open of the regular ratio Xi/Xj on the j-th
coordinate chart is exactly its intersection with the i-th chart. -/
theorem projective_coordinate_ratio_basicOpen (i j : Fin 4) :
    (P₃).basicOpen (projectiveCoordinateRatioSection k j i) = U j ⊓ U i := by
  ext p
  change p ∈ (P₃).basicOpen (projectiveCoordinateRatioSection k j i) ↔ p ∈ U j ∧ p ∈ U i
  refine (Scheme.mem_basicOpen'' P₃ (projectiveCoordinateRatioSection k j i) p).trans ?_
  have hratio (hj : p ∈ U j) :
      IsUnit ((P₃).presheaf.germ (U j) p hj (projectiveCoordinateRatioSection k j i)) ↔ p ∈ U i := by
    let e := Proj.stalkIso' G p
    have hg : e ((P₃).presheaf.germ (U j) p hj (projectiveCoordinateRatioSection k j i)) =
        projectiveCoordinateRatioAt k p j i hj :=
      Proj.stalkIso'_germ G (U j) p hj (projectiveCoordinateRatioSection k j i)
    have hunit : IsUnit (projectiveCoordinateRatioAt k p j i hj) ↔ p ∈ U i := by
      let q : ProjectiveSpectrum G := p
      change IsUnit (projectiveCoordinateRatioAt k q j i hj) ↔ (X i) ∉ q.asHomogeneousIdeal
      refine (HomogeneousLocalization.isUnit_iff_isUnit_val G q.asHomogeneousIdeal.toIdeal
        (projectiveCoordinateRatioAt k q j i hj)).symm.trans ?_
      let s : q.asHomogeneousIdeal.toIdeal.primeCompl := ⟨X j, hj⟩
      change IsUnit (Localization.mk (X i) s) ↔ (X i) ∉ q.asHomogeneousIdeal
      rw [Localization.mk_eq_mk']
      exact IsLocalization.AtPrime.isUnit_mk'_iff (Localization q.asHomogeneousIdeal.toIdeal.primeCompl)
        q.asHomogeneousIdeal.toIdeal (X i) s
    refine Iff.trans ?_ hunit
    rw [← hg]
    constructor
    · exact fun h => h.map e
    · intro h
      have he := e.symm_apply_apply
        ((P₃).presheaf.germ (U j) p hj (projectiveCoordinateRatioSection k j i))
      exact he ▸ h.map e.symm
  constructor
  · rintro ⟨hj, h⟩
    exact ⟨hj, (hratio hj).mp h⟩
  · rintro ⟨hj, h⟩
    exact ⟨hj, (hratio hj).mpr h⟩

variable (Y : Scheme.{u}) [IsIntegral Y]
  (f : Y ⟶ AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) k))
  (hU : ∀ a : Fin 4, Nonempty (f ⁻¹ᵁ
    Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (MvPolynomial.X a)))

local notation "V" a:max => f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X a)

private theorem pullbackRatio_value (i j : Fin 4) (p : V j) :
    projectivePullbackHyperplaneWeight Y f hU i =
      projectivePullbackHyperplaneWeight Y f hU j * schemeRationalSectionFunction Y (V j)
        (f.app (Proj.basicOpen G (X j)) (projectiveCoordinateRatioSection k j i)) p := by
  rw [projectivePullbackRationalCoordinate_section_at_point Y f hU]
  exact (mul_comm _ _).trans (projectivePullbackRationalCoordinate_mul Y f hU j 0 i) |>.symm

/-- The i-th homogeneous coordinate gives an actual global section
of the hyperplane sheaf, with its original regular ratios on all charts. -/
noncomputable def projectivePullbackHyperplaneCoordinateSection (i : Fin 4) :
    Γ(projectivePullbackHyperplaneModuleSheaf Y f hU, ⊤) :=
  (rationalFrameSheafSectionsLinearEquiv Y (fun j : Fin 4 => V j)
    (projectivePullbackHyperplaneWeight Y f hU) ⊤).symm
    ⟨fun _ => projectivePullbackHyperplaneWeight Y f hU i, fun _p j hp => ⟨V j, hp, le_top, le_rfl,
      f.app (Proj.basicOpen G (X j)) (projectiveCoordinateRatioSection k j i),
        pullbackRatio_value Y f hU i j⟩⟩

/-- In every original chart the actual coefficient of the coordinate
section is the regular pullback of the indicated coordinate ratio. -/
theorem projective_pullback_hyperplane_coordinate_coefficient (i j : Fin 4) :
    rationalFrameGlobalCoefficient Y (fun a : Fin 4 => V a) (projectivePullbackHyperplaneWeight Y f hU)
        (f.iSup_preimage_eq_top (polynomialProjective_basicOpen_iSup k))
        (projectivePullbackHyperplaneWeight_ne_zero Y f hU)
        (projectivePullbackHyperplaneCoordinateSection Y f hU i) j =
      f.app (Proj.basicOpen G (X j)) (projectiveCoordinateRatioSection k j i) := by
  apply ((rationalFrameGlobalSection_existsUnique_coefficient Y (fun a : Fin 4 => V a)
    (projectivePullbackHyperplaneWeight Y f hU)
    (f.iSup_preimage_eq_top (polynomialProjective_basicOpen_iSup k))
    (projectivePullbackHyperplaneCoordinateSection Y f hU i) j
    (projectivePullbackHyperplaneWeight_ne_zero Y f hU j)).choose_spec.2 _ ?_).symm
  intro p
  change projectivePullbackHyperplaneWeight Y f hU i = _
  exact pullbackRatio_value Y f hU i j p

/-- Each actual global coordinate section has the corresponding
inverse coordinate chart as its full nonvanishing open. For an affine
map these opens are affine, so on a quasi-compact source they give the
affine nonvanishing-cover criterion for ampleness in degree one. -/
theorem projective_pullback_hyperplane_affine_nonvanishing_cover
    [CompactSpace Y] [IsAffineHom f] :
    SchemeModuleIsLocallyFreeRankOne (projectivePullbackHyperplaneModuleSheaf Y f hU) ∧
      IsCompact (Set.univ : Set Y) ∧
      (⨆ i : Fin 4, V i) = ⊤ ∧
      ∀ i : Fin 4, IsAffineOpen (V i) ∧ ∀ j : Fin 4,
        Y.basicOpen (rationalFrameGlobalCoefficient Y (fun a : Fin 4 => V a)
          (projectivePullbackHyperplaneWeight Y f hU)
          (f.iSup_preimage_eq_top (polynomialProjective_basicOpen_iSup k))
          (projectivePullbackHyperplaneWeight_ne_zero Y f hU)
          (projectivePullbackHyperplaneCoordinateSection Y f hU i) j) = V j ⊓ V i := by
  have hc := f.iSup_preimage_eq_top (polynomialProjective_basicOpen_iSup k)
  refine ⟨projectivePullbackHyperplaneModuleSheaf_locallyFreeRankOne Y f hU hc,
    isCompact_univ, hc, fun i => ⟨?_, ?_⟩⟩
  · exact (Proj.isAffineOpen_basicOpen G (X i) (isHomogeneous_X (R := k) i)
      (by decide : 0 < 1)).preimage f
  · intro j
    rw [projective_pullback_hyperplane_coordinate_coefficient, ← Scheme.preimage_basicOpen,
      projective_coordinate_ratio_basicOpen, Scheme.Hom.preimage_inf]

end DimensionFourDependence
