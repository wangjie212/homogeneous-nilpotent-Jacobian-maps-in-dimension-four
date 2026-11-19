import DimensionFourDependence.SegreRulingHyperplaneDeterminant
import DimensionFourDependence.AlgebraicParameterReflection
import DimensionFourDependence.ProjectivePrimeBaseExtension

/-! # Fixed hyperplanes meeting both actual generic rulings are proportional over the original field -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 3500000

variable {K E : Type u} [Field K] [Field E] [Algebra K E]

/-- A common actual infinity point on a transcendental original
ruling forces the entire original constant ruling determinant polynomial
to vanish. No rational choice of the selected point is assumed. -/
theorem transcendental_segre_ruling_common_hyperplane_point_determinant_zero
    (t : E) (ht : Transcendental K t) (j : Fin 3) (hj : j ≠ 0)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hinfty : X none ∈ p.asHomogeneousIdeal)
    (hR0 : segreRulingLinearPolynomial t j.castSucc 0 ∈ p.asHomogeneousIdeal)
    (hR1 : segreRulingLinearPolynomial t 3 (if j = 1 then 2 else 1) ∈ p.asHomogeneousIdeal)
    (a l : Fin 4 → K)
    (ha : rename some (linearFormPolynomial (fun i => algebraMap K E (a i))) ∈ p.asHomogeneousIdeal)
    (hl : rename some (linearFormPolynomial (fun i => algebraMap K E (l i))) ∈ p.asHomogeneousIdeal) :
    segreRulingHyperplaneDeterminant j a l = 0 := by
  obtain ⟨z, hz⟩ := projective_infinity_prime_exists_direction_coordinate_not_mem p hinfty
  let κ := projectivePrimeRatioField p (some z)
  let v : Fin 4 → κ := fun i => projectivePrimeRatioCoordinate p (some z) (some i)
  let τ := algebraMap E κ t
  have hnone : projectivePrimeRatioCoordinate p (some z) none = 0 :=
    projectivePrimeRatioCoordinate_zero_of_mem p (some z) none hinfty
  have hv : v ≠ 0 := by
    intro h
    apply projectivePrimeRatioCoordinate_ne_zero p (some z) hz
    funext i
    cases i with
    | none => exact hnone
    | some i => exact congrFun h i
  have h0 := segre_normalized_projective_ruling_linear_equation p z hz t j.castSucc 0 hR0
  have h1 := segre_normalized_projective_ruling_linear_equation p z hz t 3 (if j = 1 then 2 else 1) hR1
  have hkernel : segreRulingMatrix j τ *ᵥ v = 0 := by
    rw [segreRulingMatrix_mulVec]
    fin_cases j
    · exact False.elim (hj rfl)
    · funext i
      fin_cases i
      · exact h0
      · exact h1
    · funext i
      fin_cases i
      · exact h0
      · exact h1
  let w : Fin 2 → κ := ![v 0, v (segreRulingRemainingIndex j).castSucc]
  have hw : w ≠ 0 := segre_ruling_kernel_radial_varying_pair_ne_zero j hj τ v hv hkernel
  have hpair (c : Fin 4 → K)
      (hc : rename some (linearFormPolynomial (fun i => algebraMap K E (c i))) ∈ p.asHomogeneousIdeal) :
      ((fun i => algebraMap K κ (c i)) ⬝ᵥ v) = 0 := by
    rw [← projectivePrimeRatioCoordinate_represents p (some z) hz] at hc
    have he := (projectiveFieldPoint_homogeneous_mem _
      (projectivePrimeRatioCoordinate_ne_zero p (some z) hz) _
        (linearFormPolynomial_homogeneous (fun i => algebraMap K E (c i))).rename_isHomogeneous).mp hc
    simp only [aeval_rename, Function.comp_def, linearFormPolynomial, map_sum, map_mul,
      aeval_C, aeval_X] at he
    change (∑ i, algebraMap E κ (algebraMap K E (c i)) * v i) = 0 at he
    simpa only [← IsScalarTower.algebraMap_apply K E κ, dotProduct] using he
  have hroot (c : Fin 4 → K)
      (hc : rename some (linearFormPolynomial (fun i => algebraMap K E (c i))) ∈ p.asHomogeneousIdeal) :
      segreQuadricRulingBinaryCoefficients j τ (fun i => algebraMap K κ (c i)) 0 * w 0 +
        segreQuadricRulingBinaryCoefficients j τ (fun i => algebraMap K κ (c i)) 1 * w 1 = 0 := by
    have he := hpair c hc
    rw [segre_quadric_ruling_hyperplane_binary_pairing j hj τ _ v hkernel] at he
    exact he
  have hdet := binary_covectors_common_nonzero_zero_determinant
    (segreQuadricRulingBinaryCoefficients j τ (fun i => algebraMap K κ (a i)))
    (segreQuadricRulingBinaryCoefficients j τ (fun i => algebraMap K κ (l i)))
    w hw (hroot a ha) (hroot l hl)
  have hvalue : Polynomial.eval₂ (algebraMap K κ) τ (segreRulingHyperplaneDeterminant j a l) = 0 := by
    rw [segreRulingHyperplaneDeterminant_eval₂]
    exact hdet
  have htκ : Transcendental K τ := by
    intro h
    let φ := IsScalarTower.toAlgHom K E κ
    exact ht ((isAlgebraic_algHom_iff φ φ.injective).mp h)
  by_contra hP
  exact htκ ⟨segreRulingHyperplaneDeterminant j a l, hP, hvalue⟩

variable [CharZero K]

/-- The two selected infinity points, one on each original
transcendental ruling, force the original fixed hyperplanes to be
proportional. The proof checks all determinant coefficients in the
original matrix coordinates and requires no projective-line classification. -/
theorem two_transcendental_segre_ruling_common_hyperplane_points_covectors_proportional
    (s t : E) (hs : Transcendental K s) (ht : Transcendental K t)
    (p r : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hp : SegreFirstRulingBoundaryPoint s t p) (hr : SegreSecondRulingBoundaryPoint s t r)
    (a l : Fin 4 → K) (ha0 : a ≠ 0) (hl0 : l ≠ 0)
    (hpa : rename some (linearFormPolynomial (fun i => algebraMap K E (a i))) ∈ p.asHomogeneousIdeal)
    (hra : rename some (linearFormPolynomial (fun i => algebraMap K E (a i))) ∈ r.asHomogeneousIdeal)
    (hpl : rename some (linearFormPolynomial (fun i => algebraMap K E (l i))) ∈ p.asHomogeneousIdeal)
    (hrl : rename some (linearFormPolynomial (fun i => algebraMap K E (l i))) ∈ r.asHomogeneousIdeal) :
    ∃ α : K, α ≠ 0 ∧ ∀ i, l i = α * a i := by
  have hfirst := transcendental_segre_ruling_common_hyperplane_point_determinant_zero
    t ht 2 (by decide) p hp.1 hp.2.1 hp.2.2.1 a l hpa hpl
  have hsecond := transcendental_segre_ruling_common_hyperplane_point_determinant_zero
    s hs 1 (by decide) r hr.1 hr.2.1 hr.2.2.1 a l hra hrl
  exact two_segre_ruling_hyperplane_determinants_zero_covectors_proportional a l ha0 hl0 hfirst hsecond

end DimensionFourDependence
