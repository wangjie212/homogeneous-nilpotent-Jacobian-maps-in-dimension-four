import DimensionFourDependence.PrimePencilProjectionRelation
import DimensionFourDependence.FixedPlaneProjectionPolynomial
import DimensionFourDependence.HomogeneousPencilBaseExistence

/-! # The actual tangent prime constructs a positive homogeneous fixed-coordinate base equation -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 3500000

variable {K : Type u} [Field K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "A₀" => MvPolynomial (Fin 2) K

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The two source equations generate an actually homogeneous ideal,
even when their positive homogeneous degrees are different. -/
theorem homogeneous_source_pair_span_isHomogeneous
    (p q : R₀) {d e : ℕ} (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous e) :
    (Ideal.span ({p, q} : Set R₀)).IsHomogeneous (homogeneousSubmodule (Fin 4) K) := by
  apply Ideal.homogeneous_span
  intro r hr
  rcases hr with rfl | rfl
  · exact ⟨d, hp⟩
  · exact ⟨e, hq⟩

/-- Origin evaluation makes the actual positive homogeneous
two-equation ideal proper, without requiring equal source degrees. -/
theorem positive_homogeneous_source_pair_different_degrees_span_ne_top
    (p q : R₀) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous e) :
    Ideal.span ({p, q} : Set R₀) ≠ ⊤ := by
  let J : Ideal R₀ := RingHom.ker (aeval (0 : Fin 4 → K)).toRingHom
  have hJ : J.IsPrime := RingHom.ker_isPrime _
  have hle : Ideal.span ({p, q} : Set R₀) ≤ J := by
    apply Ideal.span_le.mpr
    intro r hr
    rcases hr with rfl | rfl
    · exact positive_homogeneous_polynomial_aeval_origin _ hd hp
    · exact positive_homogeneous_polynomial_aeval_origin _ he hq
  intro hz
  exact hJ.ne_top (top_le_iff.mp (hz ▸ hle))

/-- Homogeneous extraction stays inside the actual source ideal and
inside the same two fixed coefficient coordinates. Properness rules
out a nonzero constant, so the extracted equation has positive degree. -/
theorem homogeneous_source_ideal_fixed_plane_equation_constructs_positive_homogeneous_equation
    (I : Ideal R₀) (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 4) K)) (hproper : I ≠ ⊤)
    (a : A₀) (ha : a ≠ 0) (haI : fixedPlaneCoefficientMap K a ∈ I) :
    ∃ (b : A₀) (N : ℕ), 0 < N ∧ b ≠ 0 ∧ b.IsHomogeneous N ∧ fixedPlaneCoefficientMap K b ∈ I := by
  classical
  obtain ⟨N, hN⟩ : ∃ N, homogeneousComponent N a ≠ 0 := by
    by_contra hn
    push Not at hn
    apply ha
    rw [← sum_homogeneousComponent a]
    exact Finset.sum_eq_zero (fun N _ => hn N)
  let b := homogeneousComponent N a
  have hbH : b.IsHomogeneous N := homogeneousComponent_isHomogeneous N a
  have hmap : fixedPlaneCoefficientMap K b = homogeneousComponent N (fixedPlaneCoefficientMap K a) :=
    rename_homogeneousComponent N a
  have hbI : fixedPlaneCoefficientMap K b ∈ I := by
    rw [hmap]
    exact homogeneousComponent_mem_of_mem hI haI N
  have hbmap0 : fixedPlaneCoefficientMap K b ≠ 0 :=
    fun hz => hN (fixedPlaneCoefficientMap_injective K (hz.trans (map_zero _).symm))
  have hmapH : (fixedPlaneCoefficientMap K b).IsHomogeneous N := hbH.rename_isHomogeneous
  have hpos : 0 < N := by
    by_contra hn
    have hz : N = 0 := by omega
    exact hproper (I.eq_top_of_isUnit_mem hbI (isUnit_of_isHomogeneous_zero (hz ▸ hmapH) hbmap0))
  exact ⟨b, N, hpos, hN, hbH, hbI⟩

variable [CharZero K]

/-- The original homogeneous prime tangent equation constructs a
univariate equation over the two fixed original coordinates with a
nonzero constant coefficient. -/
theorem homogeneous_prime_tangent_minor_constructs_projection_polynomial_with_nonzero_constant
    (δ F : R₀) (hδ : Prime δ) {e : ℕ} (hδH : δ.IsHomogeneous e)
    (hpartial : pderiv 1 δ ≠ 0) (hδF : ¬δ ∣ F)
    (hminor : δ ∣ sourceJacobianMinor F δ 1 2) :
    ∃ P : Polynomial A₀, P.coeff 0 ≠ 0 ∧ δ ∣ fixedPlaneProjectionEvaluate K F P := by
  obtain ⟨R, hR, hrelation⟩ :=
    homogeneous_prime_tangent_minor_constructs_nonzero_projection_relation δ F hδ hδH hpartial hminor
  exact prime_projection_relation_constructs_polynomial_with_nonzero_constant K δ F hδ hδF R hR hrelation

/-- The active output's actual base-ideal membership turns the
constructed projection polynomial into an actual nonzero positive
homogeneous equation in the two fixed source coordinates. -/
theorem homogeneous_prime_tangent_pencil_constructs_positive_fixed_plane_base_equation
    (δ q F : R₀) (hδ : Prime δ) {e D : ℕ} (he : 0 < e) (hD : 0 < D)
    (hδH : δ.IsHomogeneous e) (hqH : q.IsHomogeneous D)
    (hpartial : pderiv 1 δ ≠ 0) (hδF : ¬δ ∣ F)
    (hminor : δ ∣ sourceJacobianMinor F δ 1 2) (hFI : F ∈ Ideal.span {δ, q}) :
    ∃ (a : A₀) (N : ℕ), 0 < N ∧ a ≠ 0 ∧ a.IsHomogeneous N ∧
      fixedPlaneCoefficientMap K a ∈ Ideal.span {δ, q} := by
  obtain ⟨P, hP0, hdiv⟩ :=
    homogeneous_prime_tangent_minor_constructs_projection_polynomial_with_nonzero_constant δ F hδ hδH hpartial hδF hminor
  obtain ⟨_ha0, haI⟩ := prime_projection_polynomial_constructs_nonzero_fixed_plane_ideal_equation
    K δ F P hP0 hdiv (Ideal.span {δ, q}) (Ideal.subset_span (by simp)) hFI
  exact homogeneous_source_ideal_fixed_plane_equation_constructs_positive_homogeneous_equation
    (Ideal.span {δ, q}) (homogeneous_source_pair_span_isHomogeneous δ q hδH hqH)
    (positive_homogeneous_source_pair_different_degrees_span_ne_top δ q he hD hδH hqH)
    (P.coeff 0) hP0 haI

end DimensionFourDependence
