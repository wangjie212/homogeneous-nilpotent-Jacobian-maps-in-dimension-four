import DimensionFourDependence.OriginalRankTwoLinearBaseComponent

/-! # Projection in prescribed normalized coordinates constructs a primitive linear base prime -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 4000000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- The projection argument works in the prescribed normalized
coordinates and for the prescribed actual polynomial pencil. It
constructs a height-two prime containing every scalar-free output and
a nonzero fixed-plane linear form, without changing the source frame. -/
theorem prescribed_normalized_nilpotent_polynomial_pencil_constructs_primitive_linear_base_prime
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H))
    (hcol0 : ∀ i, aeval (Pi.single (0 : Fin 4) (1 : K)) (pderiv 0 (H i)) = if i = 1 then 1 else 0)
    (hcol1 : ∀ i, aeval (Pi.single (0 : Fin 4) (1 : K)) (pderiv 1 (H i)) = if i = 2 then 1 else 0)
    (p q g : R₀) {D N : ℕ} (hD : 0 < D) (hNpos : 0 < N) (hg : g ≠ 0)
    (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D) (hrel : IsRelPrime p q)
    (hp0 : aeval (Pi.single (0 : Fin 4) (1 : K)) p = 0)
    (hq1 : aeval (Pi.single (0 : Fin 4) (1 : K)) q = 1)
    (hgz : aeval (Pi.single (0 : Fin 4) (1 : K)) g ≠ 0)
    (v : Fin 4 → Polynomial K) (hVdeg : ∀ i, (v i).natDegree ≤ N)
    (hfactor : ∀ i, H i = g * homogeneousParameterPolynomialValue (v i) N p q) :
    ∃ (Q : Ideal R₀) (α β : K), Q.IsPrime ∧ Q.height = 2 ∧ (α ≠ 0 ∨ β ≠ 0) ∧
      C α * X 0 + C β * X 3 ∈ Q ∧
      ∀ i, homogeneousParameterPolynomialValue (v i) N p q ∈ Q := by
  obtain ⟨hvalue, hH1⟩ := normalized_first_jacobian_column_output_support_and_nonzero H hd hH hcol0
  obtain ⟨hpder, hv0, _hv01, _hv31, hdiv0, hdiv3⟩ :=
    normalized_parameter_output_jets_construct_nonzero_pencil_derivative_and_square_divisors
      H p q g (Pi.single (0 : Fin 4) (1 : K)) hp0 hq1 hgz v hVdeg hfactor hvalue hcol1
  have hminor := normalized_nilpotent_source_pencil_forces_active_minor_divisibility
    H p q g hg hrel (Pi.single (0 : Fin 4) (1 : K)) hp0 hq1 v hVdeg hfactor
    (hv0 2 (by decide)) (by simpa using hcol1 2) hdiv0 hdiv3 hN
  obtain ⟨δ, b, e, hδ, he, hδH, hb, hδq, _hδ0, _hb0, hδder, hδH1, hδminor⟩ :=
    simple_source_pencil_zero_constructs_homogeneous_prime_factor_with_tangent_minor p q (H 1) hpH hrel
      (Pi.single (0 : Fin 4) (1 : K)) 1 2 hp0 hpder hH1 hminor
  let I : Ideal R₀ := Ideal.span {δ, q}
  have hδI : δ ∈ I := Ideal.subset_span (by simp)
  have hqI : q ∈ I := Ideal.subset_span (by simp)
  have hpI : p ∈ I := by rw [hb]; exact I.mul_mem_right b hδI
  have hWI (i) : homogeneousParameterPolynomialValue (v i) N p q ∈ I :=
    positive_homogeneous_parameter_value_mem_source_pencil_ideal (v i) hNpos (hVdeg i) p q I hpI hqI
  have hH1I : H 1 ∈ I := by rw [hfactor 1]; exact I.mul_mem_left g (hWI 1)
  have hpartial : pderiv 1 δ ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hδder
    exact hδder rfl
  obtain ⟨Q, α, β, hQ, hheight, hab, hlinear⟩ :=
    homogeneous_prime_tangent_pencil_constructs_linear_height_two_base_component δ q (H 1)
      hδ he hD hδH hqH hδq hpartial hδH1 hδminor hH1I
  exact ⟨Q, α, β, hQ.1.1, hheight, hab, hlinear, fun i => hQ.1.2 (hWI i)⟩

/-- An actual rank-two map in prescribed normalized coordinates
constructs a primitive polynomial factor and an actual height-two
prime containing its entire primitive output vector and a nonzero
fixed-plane linear form. The construction preserves that source frame. -/
theorem normalized_homogeneous_rank_two_nilpotent_map_constructs_primitive_linear_base_prime
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 2)
    (hcol0 : ∀ i, aeval (Pi.single (0 : Fin 4) (1 : K)) (pderiv 0 (H i)) = if i = 1 then 1 else 0)
    (hcol1 : ∀ i, aeval (Pi.single (0 : Fin 4) (1 : K)) (pderiv 1 (H i)) = if i = 2 then 1 else 0) :
    ∃ (g : R₀) (W : Fin 4 → R₀) (Q : Ideal R₀) (α β : K),
      g ≠ 0 ∧ IsPrimitiveVec W ∧ (∀ i, H i = g * W i) ∧
      Q.IsPrime ∧ Q.height = 2 ∧ (α ≠ 0 ∨ β ≠ 0) ∧ C α * X 0 + C β * X 3 ∈ Q ∧ ∀ i, W i ∈ Q := by
  have hH1 := (normalized_first_jacobian_column_output_support_and_nonzero H hd hH hcol0).2
  obtain ⟨p, q, g, D, N, c, v, hD, hNpos, hg, hpH, hqH, _hgH, _hdegree, hrel,
    hp0, hq1, hgz, hVdeg, hprim, hfactor⟩ :=
    homogeneous_rank_two_map_constructs_point_normalized_primitive_source_pencil
      H hd hH hrank (Pi.single (0 : Fin 4) (1 : K)) hH1
  obtain ⟨Q, α, β, hQ, hheight, hab, hlinear, hWI⟩ :=
    prescribed_normalized_nilpotent_polynomial_pencil_constructs_primitive_linear_base_prime
      H hd hH hN hcol0 hcol1 p q g hD hNpos hg hpH hqH hrel hp0 hq1 hgz v hVdeg hfactor
  exact ⟨g, (fun i => homogeneousParameterPolynomialValue (v i) N p q), Q, α, β,
    hg, hprim, hfactor, hQ, hheight, hab, hlinear, hWI⟩

end DimensionFourDependence
