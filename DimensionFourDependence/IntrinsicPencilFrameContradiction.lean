import DimensionFourDependence.IntrinsicPrimitivePencilBase
import DimensionFourDependence.PrimitiveBaseConjugacy
import DimensionFourDependence.InverseFrameFixedPlaneCovector
import DimensionFourDependence.RankTwoPencilBaseFrameAvoidance

/-! # The intrinsic primitive-base comparison closes the normalized frame contradiction -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 4000000

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- A frame excluding every original pencil-base linear form cannot
have a freshly constructed primitive base prime containing a nonzero
fixed-plane linear form. The actual primitive-vector identities
identify the bases, and the actual inverse coordinate map constructs
the contradictory original covector and minimal prime. -/
theorem intrinsic_primitive_pencil_base_frame_exclusion_forbids_fixed_plane_prime
    (H : Fin 4 → R₀) (p q g : R₀) {D N : ℕ} (hD : 0 < D) (hN : 0 < N)
    (hp : p ≠ 0) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D) (hrel : IsRelPrime p q)
    (v : Fin 4 → Polynomial K) (hVdeg : ∀ i, (v i).natDegree ≤ N)
    (hprim : IsPrimitiveVec (fun i => homogeneousParameterPolynomialValue (v i) N p q))
    (hfactor : ∀ i, H i = g * homogeneousParameterPolynomialValue (v i) N p q)
    (T S : Matrix (Fin 4) (Fin 4) K) (hTS : T * S = 1) (hST : S * T = 1)
    (havoid : ∀ R ∈ (Ideal.span ({p, q} : Set R₀)).minimalPrimes,
      ∀ w : Fin 4 → K, linearFormPolynomial w ∈ R → w ≠ 0 →
        linearPolynomialPullback T (linearFormPolynomial w) ∉ Set.range (fixedPlaneCoefficientMap K))
    (B : Fin 4 → R₀) (h : R₀) (hh : h ≠ 0) (hB : IsPrimitiveVec B)
    (hnew : ∀ i, linearPolynomialConjugate T S H i = h * B i)
    (Q : Ideal R₀) [Q.IsPrime] (hheight : Q.height = 2)
    (α β : K) (hab : α ≠ 0 ∨ β ≠ 0) (hlinear : C α * X 0 + C β * X 3 ∈ Q)
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
    fixed_plane_linear_form_constructs_nonzero_inverse_frame_covector T S hTS hST Q α β hab hlinear
  exact havoid R hRmin w hwR hw0 hfixed

end DimensionFourDependence
