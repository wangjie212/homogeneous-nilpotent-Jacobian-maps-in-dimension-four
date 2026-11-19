import DimensionFourDependence.TernaryCovectorPlaneCover
import DimensionFourDependence.TernaryFiniteOrbitFrame
import DimensionFourDependence.TernaryCovectorFrameExclusion
import DimensionFourDependence.TernaryFixedAxisPrime

/-! # All actual ternary pencil base components admit simultaneous frame exclusion -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 4500000

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 3) K

theorem ternary_source_pencil_base_components_construct_finite_covector_plane_cover
    (p q : R₀) :
    ∃ F : Finset ((Fin 3 → K) × (Fin 3 → K)),
      (∀ c ∈ F, LinearIndependent K ![c.1, c.2]) ∧
      ∀ Q ∈ (Ideal.span ({p, q} : Set R₀)).minimalPrimes,
        ∃ c ∈ F, ∀ w : Fin 3 → K, linearFormPolynomial w ∈ Q →
          w ∈ Submodule.span K ({c.1, c.2} : Set (Fin 3 → K)) := by
  classical
  let I : Ideal R₀ := Ideal.span {p, q}
  let J := {Q : Ideal R₀ // Q ∈ I.minimalPrimes}
  letI : Fintype J := (Ideal.finite_minimalPrimes_of_isNoetherianRing R₀ I).fintype
  have hc (Q : J) : ∃ μ ν : Fin 3 → K, LinearIndependent K ![μ, ν] ∧
      ∀ w : Fin 3 → K, linearFormPolynomial w ∈ Q.val →
        w ∈ Submodule.span K ({μ, ν} : Set (Fin 3 → K)) := by
    let : Q.val.IsPrime := Q.property.1.1
    exact ternary_height_le_two_prime_constructs_independent_covector_covering_plane Q.val
      (two_equation_minimal_prime_height_le_two_general p q Q.val Q.property)
  choose μ ν hli hcover using hc
  let F : Finset ((Fin 3 → K) × (Fin 3 → K)) := Finset.univ.image (fun Q : J => (μ Q, ν Q))
  refine ⟨F, ?_, ?_⟩
  · intro c hcF
    obtain ⟨Q, _hQ, rfl⟩ := Finset.mem_image.mp hcF
    exact hli Q
  · intro Q hQ
    let Q' : J := ⟨Q, hQ⟩
    exact ⟨(μ Q', ν Q'), Finset.mem_image.mpr ⟨Q', Finset.mem_univ _, rfl⟩, hcover Q'⟩

/-- The actual nonzero source minors construct one normalized frame
that simultaneously excludes every nonzero original constant linear
form in every minimal prime of the prescribed source pencil base.
Neither the base components nor their covector-plane covers are given. -/
theorem ternary_nonzero_original_covector_orbit_minors_construct_normalized_frame_avoiding_pencil_base_linear_forms
    (H : Fin 3 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hind : ¬ComponentsDependent H)
    (hminors : ∀ (μ ν : Fin 3 → K), LinearIndependent K ![μ, ν] →
      outputLinearCombination H μ * outputLinearCombination (jac H *ᵥ H) ν -
        outputLinearCombination H ν * outputLinearCombination (jac H *ᵥ H) μ ≠ 0)
    (p q : R₀) :
    ∃ T S : Matrix (Fin 3) (Fin 3) K, T * S = 1 ∧ S * T = 1 ∧
      (∀ i, aeval (Pi.single (0 : Fin 3) (1 : K))
        (pderiv 0 (linearPolynomialConjugate T S H i)) = if i = 1 then 1 else 0) ∧
      (∀ i, aeval (Pi.single (0 : Fin 3) (1 : K))
        (pderiv 1 (linearPolynomialConjugate T S H i)) = if i = 2 then 1 else 0) ∧
      ∀ Q ∈ (Ideal.span ({p, q} : Set R₀)).minimalPrimes,
        ∀ w : Fin 3 → K, linearFormPolynomial w ∈ Q → w ≠ 0 →
          linearPolynomialPullback T (linearFormPolynomial w) ∉ Set.range (ternaryFixedAxisCoefficientMap K) := by
  obtain ⟨F, hF, hcover⟩ := ternary_source_pencil_base_components_construct_finite_covector_plane_cover p q
  have hW := independent_positive_homogeneous_ternary_second_jacobian_orbit_ne_zero H hd hH hind
  obtain ⟨T, S, hTS, hST, hj0, hj1, hdet⟩ :=
    ternary_finite_nonzero_covector_orbit_minors_construct_normalized_avoiding_frame H hd hH hN hW F
      (fun c hc => hminors c.1 c.2 (hF c hc))
  refine ⟨T, S, hTS, hST, hj0, hj1, ?_⟩
  intro Q hQ w hw hw0
  obtain ⟨c, hc, hcw⟩ := hcover Q hQ
  exact ternary_nonzero_covector_column_minor_excludes_entire_plane T c.1 c.2 (hdet c hc) w (hcw w hw) hw0

end DimensionFourDependence
