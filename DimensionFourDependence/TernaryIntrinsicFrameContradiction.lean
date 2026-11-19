import DimensionFourDependence.IntrinsicPrimitivePencilBase
import DimensionFourDependence.PrimitiveBaseConjugacy
import DimensionFourDependence.TernaryPencilBaseFrameAvoidance

/-! # The intrinsic ternary pencil base closes the fixed-axis frame contradiction -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 4000000

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 3) K

/-- The fixed new coordinate constructs an actual nonzero original
covector in the contracted source prime, with its exact forward value
in the original fixed-axis polynomial ring. -/
theorem ternary_fixed_coordinate_in_prime_constructs_nonzero_inverse_frame_covector
    (T S : Matrix (Fin 3) (Fin 3) K) (hTS : T * S = 1) (hST : S * T = 1)
    (Q : Ideal R₀) (hX : X (0 : Fin 3) ∈ Q) :
    ∃ w : Fin 3 → K, w ≠ 0 ∧
      linearFormPolynomial w ∈ Q.comap (matrixPolynomialCoordinateEquiv T S hTS hST).toRingHom ∧
      linearPolynomialPullback T (linearFormPolynomial w) ∈ Set.range (ternaryFixedAxisCoefficientMap K) := by
  let c : Fin 3 → K := Pi.single 0 1
  let w : Fin 3 → K := c ᵥ* S
  have hw0 : w ≠ 0 := by
    intro hz
    have he := congrArg (fun v : Fin 3 → K => v ᵥ* T) hz
    have hc0 : c = 0 := by
      simpa only [w, Matrix.vecMul_vecMul, hST, Matrix.vecMul_one, Matrix.zero_vecMul] using he
    have hone : (1 : K) = 0 := by simpa [c] using congrFun hc0 0
    exact one_ne_zero hone
  have hL : linearFormPolynomial c = X (0 : Fin 3) := by simp [linearFormPolynomial, c, Pi.single_apply]
  have hback : linearFormPolynomial w = linearPolynomialPullback S (linearFormPolynomial c) := by
    rw [linearPolynomialPullback_linear_form]
    rfl
  have hforward : linearPolynomialPullback T (linearFormPolynomial w) = X (0 : Fin 3) := by
    rw [hback, matrix_linear_polynomial_substitution_inverse S T hST, hL]
  refine ⟨w, hw0, ?_, ?_⟩
  · change linearPolynomialPullback T (linearFormPolynomial w) ∈ Q
    rw [hforward]
    exact hX
  · refine ⟨X (0 : Fin 1), ?_⟩
    rw [hforward]
    simp [ternaryFixedAxisCoefficientMap]

/-- The original avoiding frame and the new actual primitive base
prime contradict one another. Polynomial-unit uniqueness identifies
the intrinsic bases, and contraction recovers an actual minimal prime
of the original coprime ternary source pencil. -/
theorem ternary_intrinsic_primitive_pencil_frame_exclusion_forbids_fixed_axis_prime
    (H : Fin 3 → R₀) (p q g : R₀) {D N : ℕ} (hD : 0 < D) (hN : 0 < N)
    (hp : p ≠ 0) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D) (hrel : IsRelPrime p q)
    (v : Fin 3 → Polynomial K) (hVdeg : ∀ i, (v i).natDegree ≤ N)
    (hprim : IsPrimitiveVec (fun i => homogeneousParameterPolynomialValue (v i) N p q))
    (hfactor : ∀ i, H i = g * homogeneousParameterPolynomialValue (v i) N p q)
    (T S : Matrix (Fin 3) (Fin 3) K) (hTS : T * S = 1) (hST : S * T = 1)
    (havoid : ∀ R ∈ (Ideal.span ({p, q} : Set R₀)).minimalPrimes,
      ∀ w : Fin 3 → K, linearFormPolynomial w ∈ R → w ≠ 0 →
        linearPolynomialPullback T (linearFormPolynomial w) ∉ Set.range (ternaryFixedAxisCoefficientMap K))
    (B : Fin 3 → R₀) (h : R₀) (hh : h ≠ 0) (hB : IsPrimitiveVec B)
    (hnew : ∀ i, linearPolynomialConjugate T S H i = h * B i)
    (Q : Ideal R₀) [Q.IsPrime] (hheight : Q.height = 2) (hX : X (0 : Fin 3) ∈ Q)
    (hBQ : ∀ i, B i ∈ Q) : False := by
  let φ := matrixPolynomialCoordinateEquiv T S hTS hST
  let R := Q.comap φ.toRingHom
  let : R.IsPrime := Ideal.comap_isPrime φ.toRingHom Q
  have hRh : R.height = 2 := (φ.toRingEquiv.height_comap Q).trans hheight
  have hsource := conjugated_primitive_factorization_prime_contains_original_source_pullbacks
    T S hTS hST H (fun i => homogeneousParameterPolynomialValue (v i) N p q) B g h hh hprim hB hfactor hnew Q hBQ
  have hWR : ∀ i, homogeneousParameterPolynomialValue (v i) N p q ∈ R := hsource
  obtain ⟨hpR, hqR⟩ :=
    (prime_contains_primitive_evaluated_positive_pencil_iff_contains_source_generators
      v hN hVdeg p q hD hpH hqH hprim R).mp hWR
  have hRmin := prime_minimal_over_relPrime_pair R hRh p q hp hpR hqR hrel
  obtain ⟨w, hw0, hwR, hfixed⟩ :=
    ternary_fixed_coordinate_in_prime_constructs_nonzero_inverse_frame_covector T S hTS hST Q hX
  exact havoid R hRmin w hwR hw0 hfixed

end DimensionFourDependence
