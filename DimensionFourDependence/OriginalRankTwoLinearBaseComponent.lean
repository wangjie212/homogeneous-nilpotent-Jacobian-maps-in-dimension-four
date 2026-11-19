import DimensionFourDependence.OriginalRankTwoPrimePencilFactor
import DimensionFourDependence.PencilProjectionLinearBaseComponent

/-! # The original rank-two map constructs a genuine pencil base component with a fixed-plane linear form -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 4000000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- A hypothetical original independent rank-two nilpotent map
constructs its own normalized coordinates and primitive polynomial
pencil, together with an actual height-two minimal prime of that
original pencil containing a nonzero original linear form in the two
fixed source coordinates. The projection relation, prime factor,
base component and linear form are all constructed internally. -/
theorem original_independent_rank_two_nilpotent_map_constructs_normalized_pencil_and_linear_height_two_base_component
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 2)
    (hind : ¬ComponentsDependent H) :
    ∃ (T S : Matrix (Fin 4) (Fin 4) K) (p q g : R₀) (D N c : ℕ) (v : Fin 4 → Polynomial K),
      T * S = 1 ∧ S * T = 1 ∧
      let G := linearPolynomialConjugate T S H
      IsHomogMap G d ∧ IsNilpotent (jac G) ∧ ¬ComponentsDependent G ∧ polyRank (jac G) = 2 ∧
      (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K)) (pderiv 0 (G i)) = if i = 1 then 1 else 0) ∧
      (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K)) (pderiv 1 (G i)) = if i = 2 then 1 else 0) ∧
      0 < D ∧ 0 < N ∧ g ≠ 0 ∧ p.IsHomogeneous D ∧ q.IsHomogeneous D ∧
      g.IsHomogeneous c ∧ c + D * N = d ∧ IsRelPrime p q ∧
      aeval (Pi.single (0 : Fin 4) (1 : K)) p = 0 ∧
      aeval (Pi.single (0 : Fin 4) (1 : K)) q = 1 ∧
      aeval (Pi.single (0 : Fin 4) (1 : K)) g ≠ 0 ∧
      aeval (Pi.single (0 : Fin 4) (1 : K)) (pderiv 1 p) ≠ 0 ∧
      (∀ i, (v i).natDegree ≤ N) ∧
      IsPrimitiveVec (fun i => homogeneousParameterPolynomialValue (v i) N p q) ∧
      (∀ i, G i = g * homogeneousParameterPolynomialValue (v i) N p q) ∧
      ∃ (Q : Ideal R₀) (α β : K), Q ∈ (Ideal.span ({p, q} : Set R₀)).minimalPrimes ∧
        Q.height = 2 ∧ (α ≠ 0 ∨ β ≠ 0) ∧ C α * X 0 + C β * X 3 ∈ Q ∧ ∀ i, G i ∈ Q := by
  obtain ⟨T, S, hTS, hST, hGhom, hGnil, hGind, hrG, hcol0, hcol1,
    p, q, g, D, N, c, v, hD, hNpos, hg, hpH, hqH, hgH, hdegree, hrel,
    hp0, hq1, hgz, hpder, hVdeg, hprim, hfactor, _hv0, _hv01, _hv31, _hdiv0, _hdiv3, hminor⟩ :=
    original_independent_rank_two_nilpotent_map_constructs_normalized_primitive_pencil_and_double_divisors
      H hd hH hN hrank hind
  let G := linearPolynomialConjugate T S H
  have hG1 := (normalized_first_jacobian_column_output_support_and_nonzero G hd hGhom hcol0).2
  obtain ⟨δ, b, e, hδ, he, hδH, hb, hδq, _hδ0, _hb0, hδder, hδG1, hδminor⟩ :=
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
  have hpartial : pderiv 1 δ ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hδder
    exact hδder rfl
  obtain ⟨Q, α, β, hQ, hheight, hab, hlinear⟩ :=
    homogeneous_prime_tangent_pencil_constructs_linear_height_two_base_component δ q (G 1) hδ he hD hδH hqH hδq
      hpartial hδG1 hδminor (hGI 1)
  letI : Q.IsPrime := hQ.1.1
  have hpQ : p ∈ Q := hQ.1.2 hpI
  have hqQ : q ∈ Q := hQ.1.2 hqI
  have hpne : p ≠ 0 := by
    intro hz
    rw [hz, map_zero, map_zero] at hpder
    exact hpder rfl
  have hQoriginal := prime_minimal_over_relPrime_pair Q hheight p q hpne hpQ hqQ hrel
  exact ⟨T, S, p, q, g, D, N, c, v, hTS, hST, hGhom, hGnil, hGind, hrG, hcol0, hcol1,
    hD, hNpos, hg, hpH, hqH, hgH, hdegree, hrel, hp0, hq1, hgz, hpder, hVdeg, hprim, hfactor,
    Q, α, β, hQoriginal, hheight, hab, hlinear, (fun i => hQ.1.2 (hGI i))⟩

end DimensionFourDependence
