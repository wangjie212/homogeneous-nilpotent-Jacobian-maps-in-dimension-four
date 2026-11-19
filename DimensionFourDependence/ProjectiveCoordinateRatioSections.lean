import DimensionFourDependence.ProjectiveSourceSchemeChart

/-! # Original homogeneous coordinate ratios as actual projective sections -/

namespace DimensionFourDependence

open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
open TopologicalSpace Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (C : Type u) [Field C]

local notation "𝒢" => homogeneousSubmodule (Fin 4) C
local notation "P" => AlgebraicGeometry.Proj 𝒢
local notation "U" a:max => Proj.basicOpen 𝒢 (X a)

/-- The original ratio Xi/Xa in the homogeneous local ring at a
projective point where Xa is invertible. -/
noncomputable def projectiveCoordinateRatioAt (p : ProjectiveSpectrum 𝒢)
    (a i : Fin 4) (ha : X a ∉ p.asHomogeneousIdeal) :
    HomogeneousLocalization 𝒢 p.asHomogeneousIdeal.toIdeal.primeCompl :=
  .mk ⟨1, ⟨X i, isHomogeneous_X (R := C) i⟩, ⟨X a, isHomogeneous_X (R := C) a⟩, ha⟩

/-- The ratio Xa/Xa is one in the actual homogeneous local ring. -/
theorem projectiveCoordinateRatioAt_self (p : ProjectiveSpectrum 𝒢)
    (a : Fin 4) (ha : X a ∉ p.asHomogeneousIdeal) :
    projectiveCoordinateRatioAt C p a a ha = 1 := by
  rw [HomogeneousLocalization.ext_iff_val]
  simp only [projectiveCoordinateRatioAt, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_one]
  change Localization.mk (X a) (⟨X a, ha⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl) = 1
  exact Localization.mk_self (⟨X a, ha⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl)

/-- Original coordinate ratios satisfy cancellation in the actual
homogeneous local ring, with both denominators regular at the point. -/
theorem projectiveCoordinateRatioAt_mul (p : ProjectiveSpectrum 𝒢)
    (a b i : Fin 4) (ha : X a ∉ p.asHomogeneousIdeal)
    (hb : X b ∉ p.asHomogeneousIdeal) :
    projectiveCoordinateRatioAt C p a i ha * projectiveCoordinateRatioAt C p b a hb =
      projectiveCoordinateRatioAt C p b i hb := by
  rw [HomogeneousLocalization.ext_iff_val]
  simp only [projectiveCoordinateRatioAt, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_mk]
  change Localization.mk (X i) (⟨X a, ha⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl) * Localization.mk (X a) (⟨X b, hb⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl) =
    Localization.mk (X i) (⟨X b, hb⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl)
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

/-- The original coordinate ratio Xi/Xa is a genuine regular section
of the structure sheaf on the original projective Xa chart. -/
noncomputable def projectiveCoordinateRatioSection (a i : Fin 4) : Γ(P, U a) := by
  refine ⟨(fun p => projectiveCoordinateRatioAt C p.1 a i p.2), ?_⟩
  intro p
  exact ⟨U a, p.2, 𝟙 _, 1, ⟨X i, isHomogeneous_X (R := C) i⟩,
    ⟨X a, isHomogeneous_X (R := C) a⟩, (fun q => q.2), (fun q => rfl)⟩

/-- Evaluation of the actual projective section gives the original
homogeneous coordinate fraction at every point of the chart. -/
theorem projectiveCoordinateRatioSection_apply (a i : Fin 4) (p : U a) :
    (projectiveCoordinateRatioSection C a i).val p =
      projectiveCoordinateRatioAt C p.1 a i p.2 := rfl

/-- The selected frame coordinate is the unit section. -/
theorem projectiveCoordinateRatioSection_self (a : Fin 4) :
    projectiveCoordinateRatioSection C a a = 1 := by
  apply Subtype.ext
  funext p
  exact projectiveCoordinateRatioAt_self C p.1 a p.2

/-- The actual regular coordinate sections satisfy their original
cross-chart ratio identity on the actual projective overlap. -/
theorem projectiveCoordinateRatioSection_overlap (a b i : Fin 4) :
    (P).presheaf.map (Opens.infLELeft (U a) (U b)).op
        (projectiveCoordinateRatioSection C a i) *
      (P).presheaf.map (Opens.infLERight (U a) (U b)).op
        (projectiveCoordinateRatioSection C b a) =
      (P).presheaf.map (Opens.infLERight (U a) (U b)).op
        (projectiveCoordinateRatioSection C b i) := by
  apply Subtype.ext
  funext p
  exact projectiveCoordinateRatioAt_mul C p.1 a b i p.2.1 p.2.2

end DimensionFourDependence
