import DimensionFourDependence.ProjectiveBoundaryImageClosure
import DimensionFourDependence.ActualBoundaryNonGeneric
import DimensionFourDependence.RulingScalarExtensionDensity

/-! # The actual developable boundary has proper closed source image -/

namespace DimensionFourDependence

open MvPolynomial Matrix Topology

attribute [local instance] MvPolynomial.gradedAlgebra coefficientFieldScalarTower

universe u
set_option maxHeartbeats 4600000
set_option synthInstance.maxHeartbeats 115000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "S₀" => FractionRing R₄
local notation "x" => (rationalCoordinate (K := K) (n := 4))

/-- The original rank-three map constructs its actual projective
infinity section. Its projected source directions have a proper closed
image closure inside the original image surface. All of its finitely
many closed generators are drawn from actual boundary directions. -/
theorem actual_developable_boundary_source_image_closure_is_proper
    (H : Fin 4 → R₄) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hr : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1) :
    ∃ p : Equiv.Perm (Fin 4), AlgebraicIndependent K
      (fun i : Fin 3 => algebraMap R₄ S₀ (H (p i.castSucc))) ∧
      let L := coefficientField (K := K) (fun i : Fin 3 => algebraMap R₄ S₀ (H (p i.castSucc)))
      let B := AffineClosureBoundary (L := L) x
      let proj := affineBoundarySourceDirection (K := K) (L := L) x
      closure (Set.range proj) ⊂ projectiveImageSet H hd hH (rank_three_polynomial_map_ne_zero H hr) ∧
      ∃ T : Set B, T.Finite ∧ closure (Set.range proj) = ⋃ b ∈ T, closure {proj b} := by
  obtain ⟨W⟩ := exists_fiber_equation_witness_polynomial H hN hr
  obtain ⟨h, c, q, _k, hh, hc, hq, _hk⟩ := fiberEquationWitness_exists_invariant_coefficients H hN hr W
  let p := W.chart
  let Y := fun i : Fin 3 => algebraMap R₄ S₀ (H (p i.castSucc))
  let L := coefficientField (K := K) Y
  let M := projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)
  let B := AffineClosureBoundary (L := L) x
  let g := projectiveImageGenericPoint H hd hH (rank_three_polynomial_map_ne_zero H hr)
  let proj := affineBoundarySourceDirection (K := K) (L := L) x
  obtain ⟨e, hA, _⟩ := actual_gauss_fiber_ruling_polynomial_density H hd hH hr hind I hGauss
  obtain ⟨a, P, _s, _ha, ha₀, _hx, hP, hpP, hHP, hdegree⟩ :=
    exists_primitive_factorization_common_degree_le_sub_two H hH hind I
  have hpoint (κ : Type u) [Field κ] [Algebra L κ] (z : Option (Fin 4) → κ)
      (hz : z ≠ 0) (hz' : (fun i => z (some i)) ≠ 0)
      (hboundary : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet (L := L) x)
      (hz₀ : z none = 0) :
      letI := ((algebraMap L κ).comp (algebraMap K L)).toAlgebra
      let b := projectiveFieldPoint (E := K) (fun i => z (some i)) hz'
      b ∈ closure {g} ∧ b ≠ g := by
    let : Algebra K κ := ((algebraMap L κ).comp (algebraMap K L)).toAlgebra
    let : IsScalarTower K L κ := IsScalarTower.of_algebraMap_eq' rfl
    have hng := actual_full_fiber_boundary_not_generic_from_invariants H hd hH
      (rank_three_polynomial_map_ne_zero H hr) hN hr hind I hGauss p W.independent h c q hh hc hq
    have hne := hng a ha₀ P (by omega) hP hpP hHP κ z hz hz' hboundary hz₀
    refine ⟨?_, hne⟩
    have hmem := actual_full_fiber_boundary_mem_original_gauss_ruling H hr p W.independent I e h hh
      hd hH hGauss c q hc hq κ z hz hboundary hz₀
    let f : M →ₐ[K] κ := (IsScalarTower.toAlgHom K L κ).comp (actualChartGaussFieldHom H hr p W.independent I)
    let : Algebra M κ := f.toRingHom.toAlgebra
    let : IsScalarTower K M κ := IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
    let Q : Fin 4 → S₀ := fun i => algebraMap R₄ S₀ (H i)
    let P₀ := MvPolynomial.map (algebraMap K M) I.equation
    have hP₀ : aeval Q P₀ = 0 := by
      change aeval Q (MvPolynomial.map (algebraMap K M) I.equation) = _
      rw [aeval_map_algebra_extension, ← aeval_polynomial_to_fraction, I.vanishing, map_zero]
    have hI := two_dimensional_matrix_kernel_generic_point_density_extension
      (actualGaussRulingMatrix H I e) hA Q (I.output_mem_actual_gauss_ruling H hd hH e)
      (actual_gauss_fiber_output_trdeg_two H hr I hGauss) P₀ hP₀ (fun i => z (some i)) hmem
    change aeval (fun i => z (some i)) (MvPolynomial.map (algebraMap K M) I.equation) = 0 at hI
    rw [aeval_map_algebra_extension] at hI
    change projectiveFieldPoint (E := K) (fun i => z (some i)) hz' ∈
      projectiveImageSet H hd hH (rank_three_polynomial_map_ne_zero H hr)
    rw [projectiveImageSet_eq_hypersurface H hd hH _ hr I]
    apply Set.singleton_subset_iff.mpr
    exact (projectiveFieldPoint_homogeneous_mem _ _ _ I.homogeneous).mpr hI
  have hb (b : B) : proj b ∈ closure {g} ∧ proj b ≠ g := by
    let κ := FractionRing (MvPolynomial (Option (Fin 4)) L ⧸ b.val.asHomogeneousIdeal.toIdeal)
    let z := projectivePrimeCoordinate b.val
    have hz := projectivePrimeCoordinate_ne_zero b.val
    have hspan : X none ∈ (Ideal.span ({X none} : Set (MvPolynomial (Option (Fin 4)) L))) :=
      Ideal.subset_span (Set.mem_singleton _)
    have hz₀ : z none = 0 := (projectivePrimeCoordinate_eq_zero_iff b.val none).mpr
      (b.property ((show Ideal.span ({X none} : Set (MvPolynomial (Option (Fin 4)) L)) ≤ _ from le_sup_right) hspan))
    have hz' : (fun i => z (some i)) ≠ 0 := by
      intro h
      apply hz
      funext i
      cases i with
      | none => exact hz₀
      | some i => exact congrFun h i
    have hboundary : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet (L := L) x := by
      rw [projectivePrimeCoordinate_represents b.val, projectiveClosureSet_eq_zeroLocus_cone]
      exact (show projectiveConeIdeal (L := L) x ≤ _ from le_sup_left).trans b.property
    exact hpoint κ z hz hz' hboundary hz₀
  refine ⟨p, W.independent, ?_, affine_boundary_source_image_closure_finite_generators (K := K) (L := L) x⟩
  exact affine_boundary_source_image_closure_is_proper x g (fun b => (hb b).1) (fun b => (hb b).2)

end DimensionFourDependence
