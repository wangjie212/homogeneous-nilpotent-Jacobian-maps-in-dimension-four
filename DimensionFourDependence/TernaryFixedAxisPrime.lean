import DimensionFourDependence.TernaryHomogeneousPencilBaseEquation

/-! # The ternary projection constructs an actual base prime containing the fixed coordinate -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 3500000

variable {K : Type u} [Field K]
local notation "R₀" => MvPolynomial (Fin 3) K

/-- The height bound for a minimal prime over two source equations,
in any Noetherian coefficient ring. -/
theorem two_equation_minimal_prime_height_le_two_general
    {A : Type*} [CommRing A] [IsNoetherianRing A] (p q : A) (Q : Ideal A)
    (hQ : Q ∈ (Ideal.span ({p, q} : Set A)).minimalPrimes) : Q.height ≤ 2 := by
  classical
  have hfin : Q ∈ (Ideal.span (↑({p, q} : Finset A) : Set A)).minimalPrimes := by simpa using hQ
  have hh := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hfin
  exact hh.trans (by exact_mod_cast (show ({p, q} : Finset A).card ≤ 2 by
    simpa using Finset.card_insert_le p ({q} : Finset A)))

/-- A homogeneous polynomial in the sole fixed coordinate is its
exact scalar value at one times that coordinate to its degree. -/
theorem ternary_fixed_axis_homogeneous_value_is_scalar_power
    (a : MvPolynomial (Fin 1) K) {N : ℕ} (ha : a.IsHomogeneous N) :
    ternaryFixedAxisCoefficientMap K a =
      X (0 : Fin 3) ^ N * C (aeval (fun _ : Fin 1 => (1 : K)) a) := by
  have hhom : ternaryFixedAxisCoefficientMap K = aeval (fun _ : Fin 1 => (X (0 : Fin 3) : R₀)) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    simp [ternaryFixedAxisCoefficientMap]
  have hconst : aeval (fun _ : Fin 1 => (1 : R₀)) a = C (aeval (fun _ : Fin 1 => (1 : K)) a) := by
    have he := comp_aeval_apply (fun _ : Fin 1 => (1 : K)) (Algebra.ofId K R₀) a
    simpa only [map_one, Algebra.ofId_apply, MvPolynomial.algebraMap_eq] using he.symm
  rw [hhom]
  have he := homogeneous_aeval_scale a ha (fun _ : Fin 1 => (1 : R₀)) (X (0 : Fin 3))
  simpa only [mul_one, hconst] using he

/-- A nonzero homogeneous fixed-axis equation in an actual prime
forces the fixed source coordinate itself into that prime. -/
theorem ternary_homogeneous_fixed_axis_equation_in_prime_forces_coordinate
    (Q : Ideal R₀) [Q.IsPrime] (a : MvPolynomial (Fin 1) K) {N : ℕ}
    (ha : a.IsHomogeneous N) (ha0 : a ≠ 0) (haQ : ternaryFixedAxisCoefficientMap K a ∈ Q) :
    X (0 : Fin 3) ∈ Q := by
  have hconstnz : aeval (fun _ : Fin 1 => (1 : K)) a ≠ 0 := by
    intro hz
    apply ha0
    apply ternaryFixedAxisCoefficientMap_injective K
    rw [ternary_fixed_axis_homogeneous_value_is_scalar_power a ha, hz, map_zero, mul_zero, map_zero]
  have hunit : IsUnit (C (aeval (fun _ : Fin 1 => (1 : K)) a) : R₀) :=
    (isUnit_iff_ne_zero.mpr hconstnz).map C
  rw [ternary_fixed_axis_homogeneous_value_is_scalar_power a ha] at haQ
  have hpow : X (0 : Fin 3) ^ N ∈ Q := ((inferInstance : Q.IsPrime).mem_or_mem haQ).resolve_right
    (fun hm => (inferInstance : Q.IsPrime).ne_top (Q.eq_top_of_isUnit_mem hm hunit))
  exact (inferInstance : Q.IsPrime).mem_of_pow_mem N hpow

variable [CharZero K]

/-- The actual prime tangent equation constructs a height-two
minimal base prime containing the fixed coordinate. Its projection
equation, nonzero constant term and homogeneous axis power are all
derived internally. -/
theorem ternary_prime_tangent_pencil_constructs_height_two_base_prime_containing_fixed_coordinate
    (δ q F : R₀) (hδ : Prime δ) {e D : ℕ} (he : 0 < e) (hD : 0 < D)
    (hδH : δ.IsHomogeneous e) (hqH : q.IsHomogeneous D) (hcop : IsRelPrime δ q)
    (hpartial : pderiv 1 δ ≠ 0) (hδF : ¬δ ∣ F)
    (hminor : δ ∣ sourceJacobianMinor F δ 1 2) (hFI : F ∈ Ideal.span {δ, q}) :
    ∃ Q : Ideal R₀, Q ∈ (Ideal.span ({δ, q} : Set R₀)).minimalPrimes ∧ Q.height = 2 ∧ X (0 : Fin 3) ∈ Q := by
  obtain ⟨a, N, _hN, ha0, ha, haI⟩ :=
    ternary_homogeneous_prime_tangent_pencil_constructs_positive_fixed_plane_base_equation
      δ q F hδ he hD hδH hqH hpartial hδF hminor hFI
  obtain ⟨⟨Q, hQ⟩⟩ := Ideal.nonempty_minimalPrimes
    (ternary_positive_homogeneous_source_pair_different_degrees_span_ne_top δ q he hD hδH hqH)
  let : Q.IsPrime := hQ.1.1
  have hle := two_equation_minimal_prime_height_le_two_general δ q Q hQ
  have hpQ : δ ∈ Q := hQ.1.2 (Ideal.subset_span (by simp))
  have hqQ : q ∈ Q := hQ.1.2 (Ideal.subset_span (by simp))
  have hge := two_le_prime_height_of_relPrime_mem Q δ q hδ.ne_zero hpQ hqQ hcop
  exact ⟨Q, hQ, le_antisymm hle hge,
    ternary_homogeneous_fixed_axis_equation_in_prime_forces_coordinate Q a ha ha0 (hQ.1.2 haI)⟩

end DimensionFourDependence
