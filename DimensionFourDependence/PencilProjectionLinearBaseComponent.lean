import DimensionFourDependence.HomogeneousPencilProjectionEquation
import DimensionFourDependence.HomogeneousFixedPlanePrimeLinearRelation

/-! # The projection equation constructs an actual height-two linear base component -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 3500000

variable {K : Type u} [Field K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "A₀" => MvPolynomial (Fin 2) K

/-- An actual homogeneous fixed-plane equation in a coprime
positive homogeneous pencil constructs a minimal base prime of height
two containing an original nonzero fixed-plane linear form. -/
theorem positive_coprime_pencil_fixed_plane_equation_constructs_linear_height_two_base_component
    (p q : R₀) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (hp0 : p ≠ 0)
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous e) (hcop : IsRelPrime p q)
    (a : A₀) {N : ℕ} (ha : a.IsHomogeneous N) (ha0 : a ≠ 0)
    (haI : fixedPlaneCoefficientMap K a ∈ Ideal.span {p, q}) :
    ∃ (Q : Ideal R₀) (α β : K), Q ∈ (Ideal.span ({p, q} : Set R₀)).minimalPrimes ∧
      Q.height = 2 ∧ (α ≠ 0 ∨ β ≠ 0) ∧ C α * X 0 + C β * X 3 ∈ Q := by
  obtain ⟨⟨Q, hQ⟩⟩ := Ideal.nonempty_minimalPrimes
    (positive_homogeneous_source_pair_different_degrees_span_ne_top p q hd he hp hq)
  letI : Q.IsPrime := hQ.1.1
  have hpQ : p ∈ Q := hQ.1.2 (Ideal.subset_span (by simp))
  have hqQ : q ∈ Q := hQ.1.2 (Ideal.subset_span (by simp))
  have hle := two_equation_base_minimal_prime_height_le_two p q Q hQ
  have hge := two_le_prime_height_of_relPrime_mem Q p q hp0 hpQ hqQ hcop
  obtain ⟨α, β, hab, hlinear⟩ := homogeneous_fixed_plane_equation_in_prime_constructs_constant_linear_form
    Q a ha ha0 (hQ.1.2 haI)
  exact ⟨Q, α, β, hQ, le_antisymm hle hge, hab, hlinear⟩

variable [CharZero K]

/-- The original tangent-minor equation alone now constructs the
actual height-two prime component and its fixed-coordinate linear
form. All quotient, projection, homogeneous extraction and prime
selection steps are discharged internally. -/
theorem homogeneous_prime_tangent_pencil_constructs_linear_height_two_base_component
    (δ q F : R₀) (hδ : Prime δ) {e D : ℕ} (he : 0 < e) (hD : 0 < D)
    (hδH : δ.IsHomogeneous e) (hqH : q.IsHomogeneous D) (hcop : IsRelPrime δ q)
    (hpartial : pderiv 1 δ ≠ 0) (hδF : ¬δ ∣ F)
    (hminor : δ ∣ sourceJacobianMinor F δ 1 2) (hFI : F ∈ Ideal.span {δ, q}) :
    ∃ (Q : Ideal R₀) (α β : K), Q ∈ (Ideal.span ({δ, q} : Set R₀)).minimalPrimes ∧
      Q.height = 2 ∧ (α ≠ 0 ∨ β ≠ 0) ∧ C α * X 0 + C β * X 3 ∈ Q := by
  obtain ⟨a, N, _hN, ha0, ha, haI⟩ :=
    homogeneous_prime_tangent_pencil_constructs_positive_fixed_plane_base_equation δ q F hδ he hD hδH hqH
      hpartial hδF hminor hFI
  exact positive_coprime_pencil_fixed_plane_equation_constructs_linear_height_two_base_component
    δ q he hD hδ.ne_zero hδH hqH hcop a ha ha0 haI

end DimensionFourDependence
