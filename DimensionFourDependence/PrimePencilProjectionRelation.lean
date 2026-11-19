import DimensionFourDependence.PrimeSourcePlaneDerivation
import DimensionFourDependence.FullDimensionDerivationConstants

/-! # The actual prime tangent equation constructs a projection relation -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 3500000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- The active tangent-minor equation on the original homogeneous
prime hypersurface constructs a nonzero polynomial relation among the
active output and the two fixed source coordinates. No coefficient
field, quotient derivation or algebraic-dependence relation is supplied. -/
theorem homogeneous_prime_tangent_minor_constructs_nonzero_projection_relation
    (δ F : R₀) (hδ : Prime δ) {e : ℕ} (hδH : δ.IsHomogeneous e)
    (hpartial : pderiv 1 δ ≠ 0) (hminor : δ ∣ sourceJacobianMinor F δ 1 2) :
    ∃ R : MvPolynomial (Fin 3) K, R ≠ 0 ∧ δ ∣ aeval ![F, X 0, X 3] R := by
  classical
  letI : (Ideal.span {δ}).IsPrime := Ideal.isPrime_span_singleton_of_prime hδ
  let L := FractionRing (R₀ ⧸ Ideal.span {δ})
  let f : R₀ →ₐ[K] L := IsScalarTower.toAlgHom K R₀ L
  let D : Derivation K L L := primeSourcePlaneFractionDerivation δ 1 2
  have hD : D ≠ 0 := homogeneous_prime_source_plane_fraction_derivation_ne_zero δ hδH 1 2 (by decide) hpartial
  have htrlt : Algebra.trdeg K L < 4 :=
    prime_equation_fraction_source_trdeg_lt_source_dimension δ hδ.ne_zero
  have htr : Algebra.trdeg K L ≤ 3 :=
    (Cardinal.lt_natCast_add_one_iff (n := 3)).mp (by convert htrlt using 1 <;> norm_num)
  let Y : Fin 3 → L := ![f F, f (X 0), f (X 3)]
  have hDF : D (f F) = 0 := by
    rw [show D (f F) = algebraMap R₀ L (sourcePlaneHamiltonian δ 1 2 F) from
      primeSourcePlaneFractionDerivation_original_polynomial δ 1 2 F,
      sourcePlaneHamiltonian_eq_minor]
    exact (prime_source_fraction_value_zero_iff_divisible δ _).mpr hminor
  have hDX0 : D (f (X 0)) = 0 := by
    rw [show D (f (X 0)) = algebraMap R₀ L (sourcePlaneHamiltonian δ 1 2 (X 0)) from
      primeSourcePlaneFractionDerivation_original_polynomial δ 1 2 (X 0),
      sourcePlaneHamiltonian_coordinate_outside δ 1 2 0 (by decide) (by decide), map_zero]
  have hDX3 : D (f (X 3)) = 0 := by
    rw [show D (f (X 3)) = algebraMap R₀ L (sourcePlaneHamiltonian δ 1 2 (X 3)) from
      primeSourcePlaneFractionDerivation_original_polynomial δ 1 2 (X 3),
      sourcePlaneHamiltonian_coordinate_outside δ 1 2 3 (by decide) (by decide), map_zero]
  have hDY (i : Fin 3) : D (Y i) = 0 := by fin_cases i <;> assumption
  obtain ⟨R, hR, hzero⟩ := nonzero_derivation_constructs_relation_among_full_dimension_constants D hD htr Y hDY
  have hpoint : (fun i => f (![F, X 0, X 3] i)) = Y := by
    funext i
    fin_cases i <;> rfl
  have he := comp_aeval_apply (![F, X 0, X 3] : Fin 3 → R₀) f R
  rw [hpoint, hzero] at he
  exact ⟨R, hR, (prime_source_fraction_value_zero_iff_divisible δ _).mp he⟩

end DimensionFourDependence
