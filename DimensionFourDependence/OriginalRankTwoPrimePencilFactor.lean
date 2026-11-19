import DimensionFourDependence.OriginalRankTwoNormalizedPencil
import DimensionFourDependence.SimplePointPrimePencilFactor

/-! # The original rank-two map constructs its simple prime numerator and actual base ideal -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 3500000

variable {K : Type u} [Field K] {n : ℕ}
local notation "P₀" => MvPolynomial (Fin n) K

/-- Every positive homogeneous parameter value belongs to every
actual source ideal containing both pencil generators. This gives
literal ideal membership, without passing to zero loci or radicals. -/
theorem positive_homogeneous_parameter_value_mem_source_pencil_ideal
    (v : Polynomial K) {N : ℕ} (hN : 0 < N) (hv : v.natDegree ≤ N)
    (p q : P₀) (I : Ideal P₀) (hp : p ∈ I) (hq : q ∈ I) :
    homogeneousParameterPolynomialValue v N p q ∈ I := by
  have hrem : p ∣ homogeneousParameterPolynomialValue v N p q - q ^ N * C (v.coeff 0) := by
    simpa only [map_zero, zero_mul, sub_zero, ← Polynomial.coeff_zero_eq_eval_zero] using
      source_pencil_divides_homogeneous_parameter_remainder v hv p q 0
  obtain ⟨b, hb⟩ := hrem
  have hremI : homogeneousParameterPolynomialValue v N p q - q ^ N * C (v.coeff 0) ∈ I := by
    rw [hb]
    exact I.mul_mem_right b hp
  have hqI : q ^ N * C (v.coeff 0) ∈ I := I.mul_mem_right _ (I.pow_mem_of_mem hq N hN)
  simpa only [sub_add_cancel] using I.add_mem hremI hqI

variable [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- A hypothetical original rank-two counterexample constructs an
actual homogeneous prime numerator through the normalized point, with
nonzero transverse derivative, relatively prime denominator and its
own active tangent-minor equation. Its two-generator base ideal
contains every original transformed output, while the prime numerator
itself does not divide the active output. -/
theorem original_independent_rank_two_nilpotent_map_constructs_simple_prime_pencil_base_and_tangent_minor
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 2)
    (hind : ¬ComponentsDependent H) :
    ∃ (T S : Matrix (Fin 4) (Fin 4) K) (p q δ : R₀) (D e : ℕ),
      T * S = 1 ∧ S * T = 1 ∧
      let G := linearPolynomialConjugate T S H
      IsHomogMap G d ∧ IsNilpotent (jac G) ∧ ¬ComponentsDependent G ∧ polyRank (jac G) = 2 ∧
      (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K)) (pderiv 0 (G i)) = if i = 1 then 1 else 0) ∧
      (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K)) (pderiv 1 (G i)) = if i = 2 then 1 else 0) ∧
      0 < D ∧ 0 < e ∧ p.IsHomogeneous D ∧ q.IsHomogeneous D ∧
      δ.IsHomogeneous e ∧ Prime δ ∧ IsRelPrime p q ∧ IsRelPrime δ q ∧ δ ∣ p ∧
      aeval (Pi.single (0 : Fin 4) (1 : K)) p = 0 ∧
      aeval (Pi.single (0 : Fin 4) (1 : K)) q = 1 ∧
      aeval (Pi.single (0 : Fin 4) (1 : K)) δ = 0 ∧
      aeval (Pi.single (0 : Fin 4) (1 : K)) (pderiv 1 δ) ≠ 0 ∧
      aeval (Pi.single (0 : Fin 4) (1 : K)) (G 1) ≠ 0 ∧ ¬δ ∣ G 1 ∧
      δ ∣ sourceJacobianMinor (G 1) δ 1 2 ∧
      ∀ i, G i ∈ Ideal.span {δ, q} := by
  obtain ⟨T, S, hTS, hST, hGhom, hGnil, hGind, hrG, hcol0, hcol1,
    p, q, g, D, N, c, v, hD, hNpos, _hg, hpH, hqH, _hgH, _hdegree, hrel,
    hp0, hq1, _hgz, hpder, hVdeg, _hprim, hfactor, _hv0, _hv01, _hv31, _hdiv0, _hdiv3, hminor⟩ :=
    original_independent_rank_two_nilpotent_map_constructs_normalized_primitive_pencil_and_double_divisors
      H hd hH hN hrank hind
  let G := linearPolynomialConjugate T S H
  have hG1 := (normalized_first_jacobian_column_output_support_and_nonzero G hd hGhom hcol0).2
  obtain ⟨δ, b, e, hδ, he, hδH, hb, hδq, hδ0, _hb0, hδder, hδG1, hδminor⟩ :=
    simple_source_pencil_zero_constructs_homogeneous_prime_factor_with_tangent_minor p q (G 1) hpH hrel
      (Pi.single (0 : Fin 4) (1 : K)) 1 2 hp0 hpder hG1 hminor
  let I : Ideal R₀ := Ideal.span {δ, q}
  have hδI : δ ∈ I := Ideal.subset_span (by simp)
  have hqI : q ∈ I := Ideal.subset_span (by simp)
  have hpI : p ∈ I := by rw [hb]; exact I.mul_mem_right b hδI
  have hGI (i) : G i ∈ I := by
    change linearPolynomialConjugate T S H i ∈ I
    rw [hfactor i]
    exact I.mul_mem_left g (positive_homogeneous_parameter_value_mem_source_pencil_ideal
      (v i) hNpos (hVdeg i) p q I hpI hqI)
  exact ⟨T, S, p, q, δ, D, e, hTS, hST, hGhom, hGnil, hGind, hrG, hcol0, hcol1,
    hD, he, hpH, hqH, hδH, hδ, hrel, hδq, ⟨b, hb⟩, hp0, hq1, hδ0, hδder,
    hG1, hδG1, hδminor, hGI⟩

end DimensionFourDependence
