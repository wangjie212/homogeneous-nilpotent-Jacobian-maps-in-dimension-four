import DimensionFourDependence.TwoDimensionalCovectorCover
import DimensionFourDependence.OriginalRankTwoFinitePlaneAvoidance

/-! # Actual finite pencil base components admit simultaneous normalized frame exclusion -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 4500000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- All actual minimal primes of a given two-equation source base
are covered by a finite family of independent constant covector planes.
Each cover contains every original constant linear form in that prime,
including primes with no linear forms or only one independent form. -/
theorem source_pencil_base_components_construct_finite_covector_plane_cover
    (p q : R₀) :
    ∃ F : Finset ((Fin 4 → K) × (Fin 4 → K)),
      (∀ c ∈ F, LinearIndependent K ![c.1, c.2]) ∧
      ∀ Q ∈ (Ideal.span ({p, q} : Set R₀)).minimalPrimes,
        ∃ c ∈ F, ∀ w : Fin 4 → K, linearFormPolynomial w ∈ Q →
          w ∈ Submodule.span K ({c.1, c.2} : Set (Fin 4 → K)) := by
  classical
  let I : Ideal R₀ := Ideal.span {p, q}
  let J := {Q : Ideal R₀ // Q ∈ I.minimalPrimes}
  letI : Fintype J := (Ideal.finite_minimalPrimes_of_isNoetherianRing R₀ I).fintype
  have hc (Q : J) : ∃ μ ν : Fin 4 → K, LinearIndependent K ![μ, ν] ∧
      ∀ w : Fin 4 → K, linearFormPolynomial w ∈ Q.val →
        w ∈ Submodule.span K ({μ, ν} : Set (Fin 4 → K)) := by
    let : Q.val.IsPrime := Q.property.1.1
    exact height_le_two_prime_constructs_independent_covector_covering_plane Q.val
      (two_equation_base_minimal_prime_height_le_two p q Q.val Q.property)
  choose μ ν hli hcover using hc
  let F : Finset ((Fin 4 → K) × (Fin 4 → K)) := Finset.univ.image (fun Q : J => (μ Q, ν Q))
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
theorem nonzero_original_covector_orbit_minors_construct_normalized_frame_avoiding_pencil_base_linear_forms
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hind : ¬ComponentsDependent H)
    (hminors : ∀ (μ ν : Fin 4 → K), LinearIndependent K ![μ, ν] →
      outputLinearCombination H μ * outputLinearCombination (jac H *ᵥ H) ν -
        outputLinearCombination H ν * outputLinearCombination (jac H *ᵥ H) μ ≠ 0)
    (p q : R₀) :
    ∃ T S : Matrix (Fin 4) (Fin 4) K, T * S = 1 ∧ S * T = 1 ∧
      (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K))
        (pderiv 0 (linearPolynomialConjugate T S H i)) = if i = 1 then 1 else 0) ∧
      (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K))
        (pderiv 1 (linearPolynomialConjugate T S H i)) = if i = 2 then 1 else 0) ∧
      ∀ Q ∈ (Ideal.span ({p, q} : Set R₀)).minimalPrimes,
        ∀ w : Fin 4 → K, linearFormPolynomial w ∈ Q → w ≠ 0 →
          linearPolynomialPullback T (linearFormPolynomial w) ∉ Set.range (fixedPlaneCoefficientMap K) := by
  obtain ⟨F, hF, hcover⟩ := source_pencil_base_components_construct_finite_covector_plane_cover p q
  have hW := original_independent_homogeneous_four_variable_squared_jacobian_euler_ne_zero H hd hH hind
  obtain ⟨T, S, hTS, hST, hj0, hj1, hdet⟩ :=
    finite_nonzero_covector_orbit_minors_construct_normalized_avoiding_frame H hd hH hN hW F
      (fun c hc => hminors c.1 c.2 (hF c hc))
  refine ⟨T, S, hTS, hST, hj0, hj1, ?_⟩
  intro Q hQ w hw hw0
  obtain ⟨c, hc, hcw⟩ := hcover Q hQ
  exact nonzero_covector_column_minor_excludes_entire_plane T c.1 c.2 (hdet c hc) w (hcw w hw) hw0

variable [IsAlgClosed K]

/-- From the original rank-two hypotheses alone, construct a
normalized map, its actual coprime source pencil with a linear base
component, and a further normalized frame simultaneously excluding
every nonzero original linear form from every component of that same
pencil base. All finite components and covector spaces are derived. -/
theorem original_independent_rank_two_nilpotent_map_constructs_frame_avoiding_actual_pencil_base_linear_forms
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 2)
    (hind : ¬ComponentsDependent H) :
    ∃ (A B : Matrix (Fin 4) (Fin 4) K) (p q : R₀), A * B = 1 ∧ B * A = 1 ∧
      let G := linearPolynomialConjugate A B H
      IsHomogMap G d ∧ IsNilpotent (jac G) ∧ ¬ComponentsDependent G ∧ polyRank (jac G) = 2 ∧
      IsRelPrime p q ∧
      (∃ (Q : Ideal R₀) (α β : K), Q ∈ (Ideal.span ({p, q} : Set R₀)).minimalPrimes ∧
        Q.height = 2 ∧ (α ≠ 0 ∨ β ≠ 0) ∧ C α * X 0 + C β * X 3 ∈ Q ∧ ∀ i, G i ∈ Q) ∧
      ∃ T S : Matrix (Fin 4) (Fin 4) K, T * S = 1 ∧ S * T = 1 ∧
        (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K))
          (pderiv 0 (linearPolynomialConjugate T S G i)) = if i = 1 then 1 else 0) ∧
        (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K))
          (pderiv 1 (linearPolynomialConjugate T S G i)) = if i = 2 then 1 else 0) ∧
        ∀ Q ∈ (Ideal.span ({p, q} : Set R₀)).minimalPrimes,
          ∀ w : Fin 4 → K, linearFormPolynomial w ∈ Q → w ≠ 0 →
            linearPolynomialPullback T (linearFormPolynomial w) ∉ Set.range (fixedPlaneCoefficientMap K) := by
  obtain ⟨A, B, hAB, hBA, hGhom, hGnil, hGind, hrG, _hcol0, _hcol1, hminors,
    p, q, Q, α, β, hrel, hQ, hheight, hab, hlinear, hGI⟩ :=
    original_independent_rank_two_nilpotent_map_constructs_all_covector_orbit_minors H hd hH hN hrank hind
  refine ⟨A, B, p, q, hAB, hBA, hGhom, hGnil, hGind, hrG, hrel,
    ⟨Q, α, β, hQ, hheight, hab, hlinear, hGI⟩, ?_⟩
  exact nonzero_original_covector_orbit_minors_construct_normalized_frame_avoiding_pencil_base_linear_forms
    (linearPolynomialConjugate A B H) hd hGhom hGnil hGind hminors p q

end DimensionFourDependence
