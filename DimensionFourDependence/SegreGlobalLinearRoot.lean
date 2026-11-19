import DimensionFourDependence.SegreOriginalGlobalFactorization
import DimensionFourDependence.HomogeneousRationalPowerLinearForm
import DimensionFourDependence.ConstantPlaneNormal

/-! # The actual global radial factors construct the paper's fixed original source linear form -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The original constant output hyperplane has exactly its original
polynomial linear combination as its value in the actual source field. -/
theorem source_output_covector_value (H : Fin 4 → R₀) (a : Fin 4 → K) :
    algebraMap R₀ S₀ (outputLinearCombination H a) =
      ((fun i => algebraMap K S₀ (a i)) ⬝ᵥ (fun i => algebraMap R₀ S₀ (H i))) := by
  simp only [outputLinearCombination, dotProduct, map_sum, map_mul,
    IsScalarTower.algebraMap_eq K R₀ S₀, ← MvPolynomial.C_eq_algebraMap]
  rfl

/-- Component independence makes every original nonzero constant
output hyperplane nonzero in the original source field. -/
theorem independent_output_covector_source_value_ne_zero
    (H : Fin 4 → R₀) (hind : ¬ComponentsDependent H) (a : Fin 4 → K) (ha : a ≠ 0) :
    ((fun i => algebraMap K S₀ (a i)) ⬝ᵥ (fun i => algebraMap R₀ S₀ (H i))) ≠ 0 := by
  rw [← source_output_covector_value]
  intro h
  have hz : outputLinearCombination H a = 0 := by
    apply IsFractionRing.injective R₀ S₀
    simpa only [map_zero] using h
  apply hind
  refine ⟨a, ha, ?_⟩
  simpa only [outputLinearCombination, MvPolynomial.smul_eq_C_mul] using hz

/-- For the actual global radial identity, normality constructs the
paper's nonzero original source linear form with its exact rational
formula and its original polynomial power identity R(H)=ell^d. -/
theorem segre_global_radial_hyperplane_identity_constructs_source_linear_root
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ComponentsDependent H) (f : S₀) (hf : f ≠ 0)
    (a b : Fin 4 → K) (hb : b ≠ 0)
    (he : f ^ d =
      ((fun i => algebraMap K S₀ (a i)) ⬝ᵥ (fun i => algebraMap R₀ S₀ (H i))) *
      ((fun i => algebraMap K S₀ (b i)) ⬝ᵥ (fun i => algebraMap R₀ S₀ (H i))) ^ d) :
    ∃ l : Fin 4 → K, l ≠ 0 ∧
      algebraMap R₀ S₀ (linearFormPolynomial l) =
        f / ((fun i => algebraMap K S₀ (b i)) ⬝ᵥ (fun i => algebraMap R₀ S₀ (H i))) ∧
      linearFormPolynomial l ^ d = outputLinearCombination H a := by
  have hB := independent_output_covector_source_value_ne_zero H hind b hb
  have hpower :
      (f / ((fun i => algebraMap K S₀ (b i)) ⬝ᵥ (fun i => algebraMap R₀ S₀ (H i)))) ^ d =
        algebraMap R₀ S₀ (outputLinearCombination H a) := by
    rw [div_pow, he, mul_div_cancel_right₀ _ (pow_ne_zero d hB), source_output_covector_value]
  exact homogeneous_rational_positive_power_root_constructs_original_linear_form
    _ (div_ne_zero hf hB) _ d hd (outputLinearCombination_homogeneous H hH a) hpower

end DimensionFourDependence
