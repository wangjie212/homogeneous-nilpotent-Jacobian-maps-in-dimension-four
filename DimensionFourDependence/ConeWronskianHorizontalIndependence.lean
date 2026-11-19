import DimensionFourDependence.RationalParameterConstants
import DimensionFourDependence.PrimitiveMapDegree

/-! # Independence of the constructed cone tangent's horizontal coefficients

A constant relation between the two horizontal Wronskians would make a
constant combination of the first and third coordinates proportional to
the second coordinate. Exact knowledge of the parameter derivative's
constant field then contradicts independence of the original three
coordinates. No varying-direction specialization is needed.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Exact original-field derivative constants turn independence of a
three-coordinate curve into independence of its two radial-eliminated
horizontal Wronskians. -/
theorem independent_three_coordinates_horizontal_wronskians_independent
    (D : Derivation K F F)
    (hconstants : ∀ r : F, D r = 0 → ∃ k : K, r = algebraMap K F k)
    (v : Fin 3 → F) (hv : LinearIndependent K v) (d : K) (hd : d ≠ 0) :
    LinearIndependent K
      (![algebraMap K F d * (v 1 * D (v 0) - D (v 1) * v 0),
        algebraMap K F d * (v 1 * D (v 2) - D (v 1) * v 2)] : Fin 2 → F) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  let r := algebraMap K F (c 0) * v 0 + algebraMap K F (c 1) * v 2
  have hDr : D r = algebraMap K F (c 0) * D (v 0) + algebraMap K F (c 1) * D (v 2) := by
    simp [r, Derivation.leibniz, smul_eq_mul]
  have hW : v 1 * D r - D (v 1) * r = 0 := by
    have hc' : algebraMap K F d * (v 1 * D r - D (v 1) * r) = 0 := by
      simp [Fin.sum_univ_succ, Algebra.smul_def] at hc
      rw [hDr]
      dsimp only [r]
      linear_combination hc
    exact (mul_eq_zero.mp hc').resolve_left (by simpa using (algebraMap K F).injective.ne hd)
  have hv1 : v 1 ≠ 0 := hv.ne_zero 1
  have hquot : D (r / v 1) = 0 := by
    rw [D.leibniz_div]
    change (v 1)⁻¹ ^ 2 * (v 1 * D r - r * D (v 1)) = 0
    rw [mul_comm r (D (v 1)), hW, mul_zero]
  obtain ⟨k, hk⟩ := hconstants _ hquot
  have hr : r = algebraMap K F k * v 1 := (div_eq_iff hv1).mp hk
  have hrelation : ∑ j : Fin 3, (![c 0, -k, c 1] : Fin 3 → K) j • v j = 0 := by
    simp [Fin.sum_univ_succ, Algebra.smul_def]
    dsimp only [r] at hr
    linear_combination hr
  have hcoeff := Fintype.linearIndependent_iff.mp hv _ hrelation
  fin_cases i
  · exact hcoeff 0
  · exact hcoeff 2

/-- Independence of the original map forces independence of its three
scalar parameter polynomials in a common-factor source presentation. -/
theorem original_cone_common_scalar_values_polynomial_curve_independent
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hind : ¬ ComponentsDependent H)
    (t y : FractionRing (MvPolynomial (Fin 4) K)) (d : ℕ) (A : Fin 3 → Polynomial K)
    (hfirst : ∀ i : Fin 3,
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i.castSucc) =
        Polynomial.aeval t (A i) * y ^ d) : LinearIndependent K A := by
  let φ : Polynomial K →ₗ[K] FractionRing (MvPolynomial (Fin 4) K) :=
    { toFun := fun p => Polynomial.aeval t p * y ^ d
      map_add' := by intro p q; simp [add_mul]
      map_smul' := by intro k p; simp [Algebra.smul_def, mul_assoc] }
  have hLI := (linearIndependent_of_componentsIndependent H hind).map'
    (IsScalarTower.toAlgHom K (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K))).toLinearMap
    (LinearMap.ker_eq_bot.mpr
      (IsFractionRing.injective (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))))
  apply LinearIndependent.of_comp φ
  convert hLI.comp Fin.castSucc (Fin.castSucc_injective 3) using 1
  funext i
  exact (hfirst i).symm

end DimensionFourDependence
