import DimensionFourDependence.SegreRulingBoundaryPoints
import DimensionFourDependence.HomogeneousProjectiveSubstitution

/-! # The two nonradial Segre ruling points in the original projective spectrum -/

namespace DimensionFourDependence

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

variable {E κ : Type*} [Field E] [Field κ] [Algebra E κ]

/-- A ruling equation in the original projective closure coordinates. -/
noncomputable def segreRulingLinearPolynomial (a : E) (i j : Fin 4) :
    MvPolynomial (Option (Fin 4)) E := X (some i) - C a * X (some j)

theorem segreRulingLinearPolynomial_homogeneous (a : E) (i j : Fin 4) :
    (segreRulingLinearPolynomial a i j).IsHomogeneous 1 :=
  (isHomogeneous_X (R := E) (some i)).sub ((isHomogeneous_X (R := E) (some j)).C_mul a)

/-- A nonradial first-ruling point at infinity, stated entirely in
Mathlib's projective spectrum over the original coefficient field. -/
def SegreFirstRulingBoundaryPoint (s t : E)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E)) : Prop :=
  X none ∈ p.asHomogeneousIdeal ∧
    segreRulingLinearPolynomial t 2 0 ∈ p.asHomogeneousIdeal ∧
    segreRulingLinearPolynomial t 3 1 ∈ p.asHomogeneousIdeal ∧
    segreRulingLinearPolynomial s 1 0 ∉ p.asHomogeneousIdeal

/-- A nonradial second-ruling point at infinity. -/
def SegreSecondRulingBoundaryPoint (s t : E)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E)) : Prop :=
  X none ∈ p.asHomogeneousIdeal ∧
    segreRulingLinearPolynomial s 1 0 ∈ p.asHomogeneousIdeal ∧
    segreRulingLinearPolynomial s 3 2 ∈ p.asHomogeneousIdeal ∧
    segreRulingLinearPolynomial t 2 0 ∉ p.asHomogeneousIdeal

/-- Ruling equations of extension-field points are detected by their
actual coordinate cross relations. -/
theorem segreRulingLinearPolynomial_field_point_mem (b : Fin 4 → κ)
    (hb : (fun j : Option (Fin 4) => j.elim 0 b) ≠ 0) (a : E) (i j : Fin 4) :
    segreRulingLinearPolynomial a i j ∈
      (projectiveFieldPoint (E := E) (fun j : Option (Fin 4) => j.elim 0 b) hb).asHomogeneousIdeal ↔
        b i - algebraMap E κ a * b j = 0 := by
  rw [projectiveFieldPoint_homogeneous_mem _ hb _ (segreRulingLinearPolynomial_homogeneous a i j)]
  simp [segreRulingLinearPolynomial]

/-- The first pole's coordinate identities give an actual nonradial
first-ruling projective point, without identifying its residue field with the constants. -/
theorem segre_field_point_first_ruling_boundary (s t : E) (b : Fin 4 → κ)
    (hb : (fun j : Option (Fin 4) => j.elim 0 b) ≠ 0)
    (h2 : b 2 = algebraMap E κ t * b 0) (h3 : b 3 = algebraMap E κ t * b 1)
    (hkey : b 1 - algebraMap E κ s * b 0 = 1) :
    SegreFirstRulingBoundaryPoint s t
      (projectiveFieldPoint (E := E) (fun j : Option (Fin 4) => j.elim 0 b) hb) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [projectiveFieldPoint_homogeneous_mem _ hb _ (isHomogeneous_X (R := E) none)]
    simp
  · exact (segreRulingLinearPolynomial_field_point_mem b hb t 2 0).mpr (sub_eq_zero.mpr h2)
  · exact (segreRulingLinearPolynomial_field_point_mem b hb t 3 1).mpr (sub_eq_zero.mpr h3)
  · rw [segreRulingLinearPolynomial_field_point_mem, hkey]
    exact one_ne_zero

/-- The other pole gives the corresponding second-ruling projective point. -/
theorem segre_field_point_second_ruling_boundary (s t : E) (b : Fin 4 → κ)
    (hb : (fun j : Option (Fin 4) => j.elim 0 b) ≠ 0)
    (h1 : b 1 = algebraMap E κ s * b 0) (h3 : b 3 = algebraMap E κ s * b 2)
    (hkey : b 2 - algebraMap E κ t * b 0 = 1) :
    SegreSecondRulingBoundaryPoint s t
      (projectiveFieldPoint (E := E) (fun j : Option (Fin 4) => j.elim 0 b) hb) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [projectiveFieldPoint_homogeneous_mem _ hb _ (isHomogeneous_X (R := E) none)]
    simp
  · exact (segreRulingLinearPolynomial_field_point_mem b hb s 1 0).mpr (sub_eq_zero.mpr h1)
  · exact (segreRulingLinearPolynomial_field_point_mem b hb s 3 2).mpr (sub_eq_zero.mpr h3)
  · rw [segreRulingLinearPolynomial_field_point_mem, hkey]
    exact one_ne_zero

/-- These two actual projective points are distinct: the first has
nonzero first transverse coordinate, and that coordinate vanishes on the second. -/
theorem segre_first_and_second_ruling_boundary_points_distinct (s t : E)
    (p q : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hp : SegreFirstRulingBoundaryPoint s t p) (hq : SegreSecondRulingBoundaryPoint s t q) : p ≠ q := by
  intro he
  subst q
  exact hp.2.2.2 hq.2.1

end DimensionFourDependence
