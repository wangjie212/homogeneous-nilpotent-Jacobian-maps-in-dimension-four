import DimensionFourDependence.FiniteParameterRemainderRoot
import DimensionFourDependence.SegreQuadricHyperplaneRestriction
import DimensionFourDependence.SegreGlobalFactorizationTransport

/-! # The actual selected ruling point belongs to the same original global remainder hyperplane -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [CharZero K] [Field E] [IsAlgClosed E] [Algebra K E]

/-- The selected point from an actual finite ruling factorization lies
on the specified original global remainder hyperplane. The actual local
and global restrictions are compared at the original derivative-one
coordinate, retaining the selected point in its own coordinate field.
No factor compatibility, root comparison or global incidence is assumed. -/
theorem segre_selected_finite_ruling_point_mem_global_remainder_hyperplane
    (Y : Fin 4 → E) (hY0 : Y 0 ≠ 0) (hSegre : Y 0 * Y 3 - Y 1 * Y 2 = 0)
    (f : E) (hf : f ≠ 0) (d : ℕ) (hd : 1 < d)
    (j : Fin 3) (hj : j ≠ 0) (D : Derivation K E E)
    (hfixed : D (Y j.castSucc / Y 0) = 0)
    (hvarying : D (Y (segreRulingRemainingIndex j).castSucc / Y 0) = 1)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hR0 : segreRulingLinearPolynomial (Y j.castSucc / Y 0) j.castSucc 0 ∈ p.asHomogeneousIdeal)
    (hR1 : segreRulingLinearPolynomial (Y j.castSucc / Y 0) 3 (if j = 1 then 2 else 1) ∈ p.asHomogeneousIdeal)
    (hfactor : SegreFiniteRadialProductFactorization K Y f d j p)
    (a b : Fin 4 → K)
    (hglobal : f ^ d = ((fun i => algebraMap K E (a i)) ⬝ᵥ Y) *
      ((fun i => algebraMap K E (b i)) ⬝ᵥ Y) ^ d) :
    MvPolynomial.rename some (linearFormPolynomial (fun i => algebraMap K E (a i))) ∈
      p.asHomogeneousIdeal := by
  obtain ⟨z, hz, C, hC, R, B, _hR, _hB, hpower, hroot, _hRY, _hBY⟩ := hfactor
  let κ := projectivePrimeRatioField p (some z)
  let J := segreProjectiveRulingParameterField K Y j p z
  let tJ : J := ⟨algebraMap E κ (Y j.castSucc / Y 0),
    IntermediateField.subset_adjoin K _ (by rfl)⟩
  let t : C := algebraMap J C tJ
  have ht : algebraMap C κ t = algebraMap E κ (Y j.castSucc / Y 0) := rfl
  let Z : Fin 3 → κ := fun i => algebraMap E κ (Y i.castSucc)
  let v : Fin 4 → κ := fun i => projectivePrimeRatioCoordinate p (some z) (some i)
  let w : Fin 2 → κ := ![v 0, v (segreRulingRemainingIndex j).castSucc]
  have hcast0 : (0 : Fin 3).castSucc = (0 : Fin 4) := by decide
  have hZ0 : Z 0 ≠ 0 := (map_ne_zero (algebraMap E κ)).mpr hY0
  have hrel : Z j = algebraMap C κ t * Z 0 := by
    rw [ht]
    change algebraMap E κ (Y j.castSucc) = algebraMap E κ (Y j.castSucc / Y 0) * algebraMap E κ (Y 0)
    rw [map_div₀]
    exact (div_mul_cancel₀ _ hZ0).symm
  have hlocalκ : (algebraMap E κ f) ^ d / Z 0 ^ (d + 1) =
      Polynomial.aeval (Z (segreRulingRemainingIndex j) / Z 0)
        (segreRulingPowerPolynomial (segreRulingBinaryCoefficients j t R)
          (segreRulingBinaryCoefficients j t B) d) := by
    rw [hpower]
    exact segre_ruling_factored_pairing_normalized_polynomial_value j hj t R B Z hZ0 hrel d
  have hlocal : algebraMap E κ (f ^ d / Y 0 ^ (d + 1)) =
      Polynomial.aeval (algebraMap E κ (Y (segreRulingRemainingIndex j).castSucc / Y 0))
        (segreRulingPowerPolynomial (segreRulingBinaryCoefficients j t R)
          (segreRulingBinaryCoefficients j t B) d) := by
    simpa only [Z, hcast0, map_div₀, map_pow] using hlocalκ
  have hkernel : segreRulingMatrix j (algebraMap E κ (Y j.castSucc / Y 0)) *ᵥ v = 0 :=
    segre_normalized_projective_ruling_kernel Y j hj p z hz hR0 hR1
  have hvrel : (fun i : Fin 3 => v i.castSucc) j =
      algebraMap C κ t * (fun i : Fin 3 => v i.castSucc) 0 := by
    rw [ht]
    exact segreRulingMatrix_kernel_coordinate_relation j hj _ v hkernel
  have hrootBinary : algebraMap C κ (segreRulingBinaryCoefficients j t R 0) * w 0 +
      algebraMap C κ (segreRulingBinaryCoefficients j t R 1) * w 1 = 0 := by
    change ((fun i => algebraMap C κ (R i)) ⬝ᵥ (fun i : Fin 3 => v i.castSucc)) = 0 at hroot
    rw [segre_ruling_covector_binary_pairing j hj t R (fun i : Fin 3 => v i.castSucc) hvrel] at hroot
    exact hroot
  let A : Fin 4 → E := fun i => algebraMap K E (a i)
  let B₀ : Fin 4 → E := fun i => algebraMap K E (b i)
  let t₀ := Y j.castSucc / Y 0
  let A₂ := segreQuadricRulingBinaryCoefficients j t₀ A
  let B₂ := segreQuadricRulingBinaryCoefficients j t₀ B₀
  have hconstant (c : Fin 4 → K) (i : Fin 2) :
      D (segreQuadricRulingBinaryCoefficients j t₀ (fun k => algebraMap K E (c k)) i) = 0 := by
    fin_cases i <;> simp [segreQuadricRulingBinaryCoefficients, t₀,
      D.leibniz, hfixed, smul_eq_mul]
  have hglobalValue : f ^ d / Y 0 ^ (d + 1) =
      (segreRulingPowerPolynomial A₂ B₂ d).eval (Y (segreRulingRemainingIndex j).castSucc / Y 0) := by
    rw [hglobal, segre_output_hyperplane_binary_pairing Y hY0 hSegre j hj A,
      segre_output_hyperplane_binary_pairing Y hY0 hSegre j hj B₀]
    simpa only [segreRulingPowerPolynomial, segreRulingAffineFactor, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X] using
      binary_linear_power_normalized_identity (Y 0) (Y (segreRulingRemainingIndex j).castSucc)
        (A₂ 0) (A₂ 1) (B₂ 0) (B₂ 1) hY0 d
  have hrootGlobal := finite_parameter_factored_value_preserves_selected_remainder_root
    D (Y (segreRulingRemainingIndex j).castSucc / Y 0) t₀ hvarying hfixed C hC
      (segreRulingBinaryCoefficients j t R) (segreRulingBinaryCoefficients j t B)
      A₂ B₂ d hd (hconstant a) (hconstant b) (f ^ d / Y 0 ^ (d + 1))
      (div_ne_zero (pow_ne_zero d hf) (pow_ne_zero _ hY0)) hlocal hglobalValue w hrootBinary
  have hpair : (fun i => algebraMap E κ (A i)) ⬝ᵥ v = 0 := by
    have he := segre_quadric_ruling_hyperplane_binary_pairing j hj (algebraMap E κ t₀)
      (fun i => algebraMap E κ (A i)) v hkernel
    rw [segreQuadricRulingBinaryCoefficients_map, segreQuadricRulingBinaryCoefficients_map] at he
    exact he.trans hrootGlobal
  rw [← projectivePrimeRatioCoordinate_represents p (some z) hz]
  apply (projectiveFieldPoint_homogeneous_mem _
    (projectivePrimeRatioCoordinate_ne_zero p (some z) hz) _
      (linearFormPolynomial_homogeneous A).rename_isHomogeneous).mpr
  simpa only [aeval_rename, Function.comp_def, linearFormPolynomial, map_sum,
    map_mul, aeval_C, aeval_X, dotProduct] using hpair

end DimensionFourDependence
