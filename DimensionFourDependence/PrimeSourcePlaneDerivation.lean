import DimensionFourDependence.PrincipalQuotientDerivation
import DimensionFourDependence.LocalizationDerivation
import DimensionFourDependence.GeneratedPointPrimeDimension
import DimensionFourDependence.NilpotentPencilMinorDivisibility

/-! # The actual tangent minor constructs a nonzero derivation of the prime source hypersurface -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 3000000

variable {K : Type u} [Field K] {n : ℕ}
local notation "R₀" => MvPolynomial (Fin n) K

/-- The original Hamiltonian derivation in the selected two source
coordinates, with the defining prime equation as its Hamiltonian. -/
noncomputable def sourcePlaneHamiltonian (δ : R₀) (j k : Fin n) : Derivation K R₀ R₀ :=
  pderiv k δ • pderiv j - pderiv j δ • pderiv k

theorem sourcePlaneHamiltonian_apply (δ f : R₀) (j k : Fin n) :
    sourcePlaneHamiltonian δ j k f = pderiv k δ * pderiv j f - pderiv j δ * pderiv k f := by
  simp only [sourcePlaneHamiltonian, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul]

theorem sourcePlaneHamiltonian_equation (δ : R₀) (j k : Fin n) :
    sourcePlaneHamiltonian δ j k δ = 0 := by
  rw [sourcePlaneHamiltonian_apply]
  ring

theorem sourcePlaneHamiltonian_eq_minor (δ f : R₀) (j k : Fin n) :
    sourcePlaneHamiltonian δ j k f = sourceJacobianMinor f δ j k := by
  rw [sourcePlaneHamiltonian_apply, sourceJacobianMinor]
  ring

theorem sourcePlaneHamiltonian_coordinate_second
    (δ : R₀) (j k : Fin n) (hjk : j ≠ k) :
    sourcePlaneHamiltonian δ j k (X k) = -pderiv j δ := by
  rw [sourcePlaneHamiltonian_apply]
  simp [hjk, Ne.symm hjk]

theorem sourcePlaneHamiltonian_coordinate_outside
    (δ : R₀) (j k i : Fin n) (hji : j ≠ i) (hki : k ≠ i) :
    sourcePlaneHamiltonian δ j k (X i) = 0 := by
  rw [sourcePlaneHamiltonian_apply]
  simp [hji, hki, Ne.symm hji, Ne.symm hki]

variable (δ : MvPolynomial (Fin n) K) [hδI : (Ideal.span {δ}).IsPrime]
local notation "Aδ" => R₀ ⧸ Ideal.span (Set.singleton δ)
local notation "Fδ" => FractionRing (R₀ ⧸ Ideal.span (Set.singleton δ))

/-- The tangent derivation on the actual fraction field of the
original principal prime quotient. Both descent and extension are
constructed from the polynomial operator. -/
noncomputable def primeSourcePlaneFractionDerivation (j k : Fin n) : Derivation K Fδ Fδ :=
  localizationDerivation (nonZeroDivisors Aδ)
    (principalQuotientDerivation (sourcePlaneHamiltonian δ j k) δ (sourcePlaneHamiltonian_equation δ j k))

/-- Every original polynomial retains its exact tangent derivative
after both quotient descent and fraction-field extension. -/
theorem primeSourcePlaneFractionDerivation_original_polynomial
    (j k : Fin n) (f : R₀) :
    primeSourcePlaneFractionDerivation δ j k (algebraMap R₀ Fδ f) =
      algebraMap R₀ Fδ (sourcePlaneHamiltonian δ j k f) := by
  rw [IsScalarTower.algebraMap_apply R₀ Aδ Fδ, IsScalarTower.algebraMap_apply R₀ Aδ Fδ]
  change localizationDerivation (nonZeroDivisors Aδ)
    (principalQuotientDerivation (sourcePlaneHamiltonian δ j k) δ (sourcePlaneHamiltonian_equation δ j k))
    (algebraMap Aδ Fδ (Ideal.Quotient.mk (Ideal.span {δ}) f)) = _
  rw [localizationDerivation_algebraMap, principalQuotientDerivation_mk]
  rfl

/-- Zero in the actual prime residue fraction field is literal
divisibility by the original source equation. -/
theorem prime_source_fraction_value_zero_iff_divisible (f : R₀) :
    algebraMap R₀ Fδ f = 0 ↔ δ ∣ f := by
  change f ∈ RingHom.ker (algebraMap R₀ Fδ) ↔ δ ∣ f
  rw [prime_quotient_fraction_algebraMap_ker]
  exact Ideal.mem_span_singleton

/-- A nonzero partial of a homogeneous prime equation survives
modulo that equation, and hence makes the constructed tangent
derivation nonzero on the actual hypersurface field. -/
theorem homogeneous_prime_source_plane_fraction_derivation_ne_zero
    {e : ℕ} (hδ : δ.IsHomogeneous e) (j k : Fin n) (hjk : j ≠ k)
    (hpartial : pderiv j δ ≠ 0) : primeSourcePlaneFractionDerivation δ j k ≠ 0 := by
  intro hz
  have he := congrArg (fun D : Derivation K Fδ Fδ => D (algebraMap R₀ Fδ (X k))) hz
  rw [primeSourcePlaneFractionDerivation_original_polynomial,
    sourcePlaneHamiltonian_coordinate_second δ j k hjk, map_neg] at he
  have hzero : algebraMap R₀ Fδ (pderiv j δ) = 0 := by simpa only [Derivation.zero_apply, neg_eq_zero] using he
  have hdiv := (prime_source_fraction_value_zero_iff_divisible δ (pderiv j δ)).mp hzero
  exact hpartial (pderiv_eq_zero_of_dvd hδ j hdiv)

/-- The fraction field of a nonzero original principal prime has
strictly smaller source dimension; no smoothness or parametrization
hypothesis is required. -/
theorem prime_equation_fraction_source_trdeg_lt_source_dimension (hδ : δ ≠ 0) :
    Algebra.trdeg K Fδ < n := by
  let I : Ideal R₀ := Ideal.span {δ}
  have hI : I ≠ ⊥ := by
    intro hz
    exact hδ (Ideal.mem_bot.mp (hz ▸ Ideal.subset_span (Set.mem_singleton δ)))
  have hdrop : Algebra.trdeg K Aδ < n :=
    (prime_quotient_trdeg_lt (K' := K) I hI
      (trdeg_lt_aleph0_of_finiteType (R := K) (S := R₀))).trans_eq (by simp)
  letI : Algebra.IsAlgebraic Aδ Fδ := IsLocalization.isAlgebraic Fδ (nonZeroDivisors Aδ)
  have heq : Algebra.trdeg K Aδ = Algebra.trdeg K Fδ := by
    have he := trdeg_add_eq (A := Fδ) K Aδ
    simpa only [trdeg_eq_zero, add_zero] using he
  exact heq ▸ hdrop

end DimensionFourDependence
