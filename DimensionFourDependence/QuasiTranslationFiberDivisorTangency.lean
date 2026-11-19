import DimensionFourDependence.QuasiTranslationInvariantDivisors

/-! # Fiber divisor tangency and the Gordan-Noether degree obstruction

The actual squarefree hypersurface over an image line divides the
constant-direction derivative of every invariant. Primitivity removes
all direction components from the divisibility conclusion. Comparing
the hypersurface degree with the homogeneous invariant's degree forces
that derivative to vanish, the algebraic core of de Bondt's (5.2).
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K] {n : ℕ}
local notation "P₀" => MvPolynomial (Fin n) K

/-- A scalar divisible after multiplication by every component of a
primitive vector was already divisible. The finite gcd is constructed. -/
theorem primitive_vector_cancels_common_scalar_divisibility
    (u : Fin n → P₀) (hprim : IsPrimitiveVec u) (a b : P₀)
    (hdiv : ∀ i, a ∣ b * u i) : a ∣ b := by
  classical
  letI : NormalizedGCDMonoid P₀ := Classical.arbitrary (NormalizedGCDMonoid P₀)
  let g := Finset.univ.gcd u
  have hunit : IsUnit g := hprim g (fun i => Finset.gcd_dvd (Finset.mem_univ i))
  have hgcd : a ∣ Finset.univ.gcd (fun i => b * u i) := Finset.dvd_gcd (fun i _ => hdiv i)
  have hbg : a ∣ b * g := hgcd.trans (Finset.gcd_mul_left' Finset.univ u b).dvd
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  obtain ⟨q, hq⟩ := hbg
  refine ⟨q * v, ?_⟩
  calc
    b = (b * g) * v := by rw [mul_assoc, hv, mul_one]
    _ = a * (q * v) := by rw [hq, mul_assoc]

variable [IsAlgClosed K]

/-- The actual affine zero locus of a squarefree polynomial detects
divisibility, with the radical principal ideal supplied internally. -/
theorem squarefree_polynomial_divides_of_vanishing_on_its_zero_locus
    (p q : P₀) (hp : Squarefree p)
    (hzero : ∀ z : Fin n → K, aeval z p = 0 → aeval z q = 0) : p ∣ q := by
  let I : Ideal P₀ := Ideal.span {p}
  have hrad : I.IsRadical := isRadical_iff_span_singleton.mp hp.isRadical
  have hq : q ∈ MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K I) := by
    intro z hz
    apply hzero z
    exact hz p (Ideal.subset_span (Set.mem_singleton p))
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hrad.radical] at hq
  exact Ideal.mem_span_singleton.mp hq

variable [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- An actual squarefree hypersurface lying over a specified image
line divides the corresponding constant derivative of every invariant.
Zeros of the direction vector cause no exception to the pointwise
argument; primitivity cancels all four components afterwards. -/
theorem primitive_line_fiber_divisor_divides_invariant_constant_derivative
    (u : Fin 4 → R₀) (hprim : IsPrimitiveVec u)
    (f : R₀) (hf : polynomialVectorDerivation u f = 0)
    (p : R₀) (hp : Squarefree p) (c : Fin 4 → K)
    (hline : ∀ z : Fin 4 → K, aeval z p = 0 → ∀ i j,
      aeval z (u i) * c j = aeval z (u j) * c i) :
    p ∣ polynomialVectorDerivation (fun j => C (c j)) f := by
  apply primitive_vector_cancels_common_scalar_divisibility u hprim
  intro i
  apply squarefree_polynomial_divides_of_vanishing_on_its_zero_locus _ _ hp
  intro z hz
  have hfv := congrArg (aeval z) hf
  simp only [polynomialVectorDerivation_apply, map_sum, map_mul, map_zero] at hfv
  simp only [polynomialVectorDerivation_apply, map_mul, map_sum, aeval_C,
    MvPolynomial.algebraMap_eq, aeval_X, Algebra.algebraMap_self, RingHom.id_apply]
  rw [Finset.sum_mul]
  calc
    (∑ j, c j * aeval z (pderiv j f) * aeval z (u i)) =
        c i * ∑ j, aeval z (u j) * aeval z (pderiv j f) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      calc
        c j * aeval z (pderiv j f) * aeval z (u i) =
            aeval z (pderiv j f) * (aeval z (u i) * c j) := by ring
        _ = aeval z (pderiv j f) * (aeval z (u j) * c i) := by rw [hline z hz i j]
        _ = _ := by ring
    _ = 0 := by rw [hfv, mul_zero]

/-- When the actual fiber divisor has at least the homogeneous
invariant's degree, tangency is global annihilation in that constant
direction. The strict degree drop of differentiation supplies the
contradiction without any assumed derivative vanishing. -/
theorem primitive_line_fiber_degree_bound_forces_invariant_constant_derivative_zero
    (u : Fin 4 → R₀) (hprim : IsPrimitiveVec u)
    (f : R₀) {d : ℕ} (hhom : f.IsHomogeneous d) (hf : polynomialVectorDerivation u f = 0)
    (p : R₀) (hp : Squarefree p) (c : Fin 4 → K)
    (hline : ∀ z : Fin 4 → K, aeval z p = 0 → ∀ i j,
      aeval z (u i) * c j = aeval z (u j) * c i)
    (hdegree : d ≤ p.totalDegree) :
    polynomialVectorDerivation (fun j => C (c j)) f = 0 := by
  by_contra hn
  have hdpos : 0 < d := by
    by_contra hd
    have he : d = 0 := by omega
    have hc := eq_C_of_isHomogeneous_zero (he ▸ hhom)
    apply hn
    exact (congrArg (polynomialVectorDerivation (fun j => C (c j))) hc).trans
      (by simp [polynomialVectorDerivation_apply])
  have hderhom : (polynomialVectorDerivation (fun j => C (c j)) f).IsHomogeneous (d - 1) := by
    rw [polynomialVectorDerivation_apply]
    exact IsHomogeneous.sum _ _ _ (fun j _ => (hhom.pderiv (i := j)).C_mul (c j))
  have hdvd := primitive_line_fiber_divisor_divides_invariant_constant_derivative u hprim f hf p hp c hline
  have hle := totalDegree_le_of_dvd_of_isDomain hdvd hn
  rw [hderhom.totalDegree hn] at hle
  omega

end DimensionFourDependence
