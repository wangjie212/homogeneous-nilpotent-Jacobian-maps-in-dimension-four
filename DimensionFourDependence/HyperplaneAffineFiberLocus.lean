import DimensionFourDependence.LinearHyperplaneGraphPoints

/-! # The projective graph identifies the actual L = 1 affine output fibers -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v w

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type u} {σ : Type v} {ι : Type w} [Field E]

/-- The homogeneous source level on its original denominator open. -/
def hyperplaneTargetLevelLocus (P : ι → MvPolynomial σ E) (d : ℕ)
    (L : MvPolynomial σ E) (Y : ι → E) : Set (ProjectiveSpectrum (homogeneousSubmodule σ E)) :=
  {z | L ∉ z.asHomogeneousIdeal ∧ ∀ i, P i - C (Y i) * L ^ d ∈ z.asHomogeneousIdeal}

/-- The actual affine fiber P(X) = Y, L(X) = 1, represented in the
standard affine chart of projective space. Its closure is taken only
after imposing that the homogenizing coordinate is nonzero. -/
def hyperplaneAffineFiberProjectiveLocus (P : ι → MvPolynomial σ E) (d : ℕ)
    (L : MvPolynomial σ E) (Y : ι → E) :
    Set (ProjectiveSpectrum (homogeneousSubmodule (Option σ) E)) :=
  {z | X none ∉ z.asHomogeneousIdeal ∧
    rename some L - X none ∈ z.asHomogeneousIdeal ∧
    ∀ i, rename some (P i) - C (Y i) * X none ^ d ∈ z.asHomogeneousIdeal}

/-- The everywhere-defined graph morphism identifies precisely the
original homogeneous target level with the L = 1 affine fiber chart. -/
theorem linearHyperplaneProjectiveGraph_mem_affine_fiber_iff
    (P : ι → MvPolynomial σ E) (d : ℕ) (L : MvPolynomial σ E) (hL : L.IsHomogeneous 1)
    (Y : ι → E) (z : ProjectiveSpectrum (homogeneousSubmodule σ E)) :
    linearHyperplaneProjectiveGraph L hL z ∈ hyperplaneAffineFiberProjectiveLocus P d L Y ↔
      z ∈ hyperplaneTargetLevelLocus P d L Y := by
  have hC (c : E) : linearHyperplaneGraphHom L (C c) = C c := by
    simp only [linearHyperplaneGraphHom, aeval_C]
    rfl
  have hzero : (0 : MvPolynomial σ E) ∈ z.asHomogeneousIdeal := Ideal.zero_mem _
  change (X none ∉ (linearHyperplaneProjectiveGraph L hL z).asHomogeneousIdeal ∧
    rename some L - X none ∈ (linearHyperplaneProjectiveGraph L hL z).asHomogeneousIdeal ∧
    ∀ i, rename some (P i) - C (Y i) * X none ^ d ∈
      (linearHyperplaneProjectiveGraph L hL z).asHomogeneousIdeal) ↔ _
  simp only [linearHyperplaneProjectiveGraph_mem_iff, map_sub, map_mul, map_pow,
    linearHyperplaneGraphHom_none, linearHyperplaneGraphHom_rename, hC, sub_self,
    hzero, true_and, hyperplaneTargetLevelLocus, Set.mem_ofPred_eq]

/-- Closure of the original homogeneous level maps into the actual
projective closure of the original affine fiber with L fixed to one. -/
theorem linearHyperplaneProjectiveGraph_maps_level_closure_into_affine_fiber_closure
    (P : ι → MvPolynomial σ E) (d : ℕ) (L : MvPolynomial σ E) (hL : L.IsHomogeneous 1)
    (Y : ι → E) (z : ProjectiveSpectrum (homogeneousSubmodule σ E))
    (hz : z ∈ closure (hyperplaneTargetLevelLocus P d L Y)) :
    linearHyperplaneProjectiveGraph L hL z ∈ closure (hyperplaneAffineFiberProjectiveLocus P d L Y) := by
  apply closure_mono _ (mem_closure_image (linearHyperplaneProjectiveGraph L hL).continuous.continuousAt hz)
  rintro _ ⟨y, hy, rfl⟩
  exact (linearHyperplaneProjectiveGraph_mem_affine_fiber_iff P d L hL Y y).mpr hy

/-- Every actual prime of this affine chart constructs its own field
coordinates satisfying exactly L = 1 and all original output equations.
This works for nonclosed primes and supplies the coefficient field. -/
theorem hyperplaneAffineFiberProjectiveLocus_constructs_actual_affine_solution
    (P : ι → MvPolynomial σ E) (d : ℕ) (hP : ∀ i, (P i).IsHomogeneous d)
    (L : MvPolynomial σ E) (hL : L.IsHomogeneous 1) (Y : ι → E)
    (z : ProjectiveSpectrum (homogeneousSubmodule (Option σ) E))
    (hz : z ∈ hyperplaneAffineFiberProjectiveLocus P d L Y) :
    aeval (fun i => projectivePrimeRatioCoordinate z none (some i)) L = 1 ∧
      ∀ i, aeval (fun j => projectivePrimeRatioCoordinate z none (some j)) (P i) =
        algebraMap E (projectivePrimeRatioField z none) (Y i) := by
  obtain ⟨hchart, hlinear, htarget⟩ := hz
  have hself := projectivePrimeRatioCoordinate_self z none hchart
  have hlin := (projectivePrimeRatioCoordinate_homogeneous_zero_iff z none hchart
    (rename some L - X none) (hL.rename_isHomogeneous.sub (isHomogeneous_X (R := E) none))).mpr hlinear
  have hLt : aeval (fun i => projectivePrimeRatioCoordinate z none (some i)) L = 1 := by
    simpa only [map_sub, aeval_rename, aeval_X, hself, sub_eq_zero, Function.comp_def] using hlin
  refine ⟨hLt, fun i => ?_⟩
  have hhom : (rename some (P i) - C (Y i) * X none ^ d).IsHomogeneous d :=
    (hP i).rename_isHomogeneous.sub ((isHomogeneous_X_pow (R := E) none d).C_mul (Y i))
  have he := (projectivePrimeRatioCoordinate_homogeneous_zero_iff z none hchart _ hhom).mpr (htarget i)
  simpa only [map_sub, map_mul, map_pow, aeval_rename, aeval_C, aeval_X, hself, one_pow,
    mul_one, sub_eq_zero, Function.comp_def] using he

end DimensionFourDependence
