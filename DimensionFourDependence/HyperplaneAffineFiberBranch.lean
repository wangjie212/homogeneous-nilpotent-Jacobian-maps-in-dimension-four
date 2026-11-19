import DimensionFourDependence.HyperplaneAffineFiberLocus
import DimensionFourDependence.LocallyClosedSpecialization
import DimensionFourDependence.ProjectiveBoundaryProjection
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Actual affine fiber branches constructed from a normalized level closure -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry TopologicalSpace CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v w

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type u} [Field E] {σ : Type v}

/-- Every projective point in the affine chart is the actual generic
point of the projective closure of its own normalized affine coordinates. -/
theorem projective_affine_chart_point_eq_closure_generic_point
    (z : ProjectiveSpectrum (homogeneousSubmodule (Option σ) E))
    (hz : X none ∉ z.asHomogeneousIdeal) :
    projectiveClosureGenericPoint (L := E)
      (fun i => projectivePrimeRatioCoordinate z none (some i)) = z := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro D P hP
  change P.IsHomogeneous D at hP
  change P ∈ projectiveConeIdeal (L := E) (fun i => projectivePrimeRatioCoordinate z none (some i)) ↔ _
  rw [projectiveConeIdeal_mem_of_isHomogeneous _ hP]
  have hcoords : (fun j : Option σ => j.elim 1
      (fun i => projectivePrimeRatioCoordinate z none (some i))) = projectivePrimeRatioCoordinate z none := by
    funext j
    cases j with
    | none => exact (projectivePrimeRatioCoordinate_self z none hz).symm
    | some i => rfl
  rw [hcoords]
  exact projectivePrimeRatioCoordinate_homogeneous_zero_iff z none hz P hP

variable {ι : Type w}

/-- A homogeneous level on a Noetherian scheme is locally closed.
Every point of its closure is a specialization of an actual point of the
same level on its prescribed denominator open. -/
theorem normalized_hyperplane_target_level_closure_constructs_specializing_point
    (X : Scheme.{max u v}) [IsNoetherian X]
    (f : X ⟶ AlgebraicGeometry.Proj (homogeneousSubmodule σ E))
    (P : ι → MvPolynomial σ E) (d : ℕ) (L : MvPolynomial σ E) (Y : ι → E)
    (z : X) (hz : z ∈ closure (f ⁻¹' hyperplaneTargetLevelLocus P d L Y)) :
    ∃ q : X, q ∈ f ⁻¹' hyperplaneTargetLevelLocus P d L Y ∧ q ⤳ z := by
  let U : Set X := f ⁻¹' (Proj.basicOpen (homogeneousSubmodule σ E) L : Set _)
  let Z : Set X := f ⁻¹' ProjectiveSpectrum.zeroLocus (homogeneousSubmodule σ E)
    (Set.range (fun i => P i - C (Y i) * L ^ d))
  have hU : IsOpen U := (Proj.basicOpen (homogeneousSubmodule σ E) L).isOpen.preimage f.continuous
  have hZ : IsClosed Z := (ProjectiveSpectrum.isClosed_zeroLocus _ _).preimage f.continuous
  have he : f ⁻¹' hyperplaneTargetLevelLocus P d L Y = U ∩ Z := by
    ext x
    change (L ∉ (f x).asHomogeneousIdeal ∧
      ∀ i, P i - C (Y i) * L ^ d ∈ (f x).asHomogeneousIdeal) ↔
      (L ∉ (f x).asHomogeneousIdeal ∧
        Set.range (fun i => P i - C (Y i) * L ^ d) ⊆ (f x).asHomogeneousIdeal)
    rw [Set.range_subset_iff]
    rfl
  rw [he] at hz
  obtain ⟨q, hq, hqz⟩ := locally_closed_closure_constructs_specializing_point U Z hU hZ z hz
  exact ⟨q, he ▸ hq, hqz⟩

/-- A specializing normalized level point supplies its actual field
of affine coordinates, all original target equations, and the specified
boundary point on that affine solution's own projective closure. -/
theorem normalized_target_level_constructs_actual_affine_solution_boundary
    (X : Scheme.{max u v}) [IsNoetherian X]
    (f : X ⟶ AlgebraicGeometry.Proj (homogeneousSubmodule σ E))
    (P : ι → MvPolynomial σ E) (d : ℕ) (hP : ∀ i, (P i).IsHomogeneous d)
    (L : MvPolynomial σ E) (hL : L.IsHomogeneous 1) (Y : ι → E)
    (z : X) (hz : z ∈ closure (f ⁻¹' hyperplaneTargetLevelLocus P d L Y)) :
    ∃ q : X, q ∈ f ⁻¹' hyperplaneTargetLevelLocus P d L Y ∧ q ⤳ z ∧
      let p := linearHyperplaneProjectiveGraph L hL (f q)
      let x := fun i => projectivePrimeRatioCoordinate p none (some i)
      aeval x L = 1 ∧ (∀ i, aeval x (P i) = algebraMap E (projectivePrimeRatioField p none) (Y i)) ∧
        linearHyperplaneProjectiveGraph L hL (f z) ∈ projectiveClosureSet (L := E) x := by
  obtain ⟨q, hq, hqz⟩ := normalized_hyperplane_target_level_closure_constructs_specializing_point
    X f P d L Y z hz
  let p := linearHyperplaneProjectiveGraph L hL (f q)
  have hp : p ∈ hyperplaneAffineFiberProjectiveLocus P d L Y :=
    (linearHyperplaneProjectiveGraph_mem_affine_fiber_iff P d L hL Y (f q)).mpr hq
  have hvalues := hyperplaneAffineFiberProjectiveLocus_constructs_actual_affine_solution P d hP L hL Y p hp
  refine ⟨q, hq, hqz, hvalues.1, hvalues.2, ?_⟩
  change linearHyperplaneProjectiveGraph L hL (f z) ∈
    closure {projectiveClosureGenericPoint (L := E) (fun i => projectivePrimeRatioCoordinate p none (some i))}
  rw [projective_affine_chart_point_eq_closure_generic_point p hp.1]
  exact specializes_iff_mem_closure.mp
    (hqz.map (f ≫ linearHyperplaneProjectiveGraph L hL).continuous)

end DimensionFourDependence
