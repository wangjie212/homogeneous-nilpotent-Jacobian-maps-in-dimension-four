import DimensionFourDependence.PrimitivePolynomialConjugacy
import DimensionFourDependence.PrimitiveVectorFactorUniqueness

/-! # The intrinsic primitive base commutes with actual inverse coordinates -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] {n : ℕ}
local notation "R₀" => MvPolynomial (Fin n) K

/-- Source-target conjugacy preserves the actual common scalar
presentation, with that scalar pulled back by the source matrix. -/
theorem linearPolynomialConjugate_common_scalar_factorization
    (T S : Matrix (Fin n) (Fin n) K) (H W : Fin n → R₀) (g : R₀)
    (hfactor : ∀ i, H i = g * W i) (i : Fin n) :
    linearPolynomialConjugate T S H i =
      linearPolynomialPullback T g * linearPolynomialConjugate T S W i := by
  simp only [linearPolynomialConjugate, linearPolynomialPullback, hfactor, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- An ideal containing all conjugated output components contains
every original output pulled back by the source coordinates. The
inverse target matrix is used explicitly. -/
theorem ideal_contains_conjugated_vector_iff_contains_source_pullbacks
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1)
    (W : Fin n → R₀) (Q : Ideal R₀) :
    (∀ i, linearPolynomialConjugate T S W i ∈ Q) ↔
      ∀ i, linearPolynomialPullback T (W i) ∈ Q := by
  have hTSC : T.map (C : K →+* R₀) * S.map C = 1 := by
    rw [← Matrix.map_mul, hTS]
    ext i j
    simp [Matrix.one_apply]
  have hrestore (i : Fin n) : linearPolynomialPullback T (W i) =
      ∑ j, C (T i j) * linearPolynomialConjugate T S W j := by
    change (fun j => linearPolynomialPullback T (W j)) i =
      (T.map C *ᵥ (S.map C *ᵥ fun j => linearPolynomialPullback T (W j))) i
    rw [Matrix.mulVec_mulVec, hTSC, Matrix.one_mulVec]
  constructor
  · intro h i
    rw [hrestore i]
    exact Q.sum_mem (fun j _ => Q.mul_mem_left _ (h j))
  · intro h i
    exact Q.sum_mem (fun j _ => Q.mul_mem_left _ (h j))

/-- The actual scalar-free base of a conjugated map agrees with the
base of any freshly constructed primitive factorization. This derives
the comparison from the two actual polynomial identities and the two
primitivity proofs, without a parameter-change hypothesis. -/
theorem conjugated_primitive_factorization_prime_contains_original_source_pullbacks
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H W B : Fin n → R₀) (g h : R₀) (hh : h ≠ 0)
    (hW : IsPrimitiveVec W) (hB : IsPrimitiveVec B)
    (hfactor : ∀ i, H i = g * W i)
    (hnew : ∀ i, linearPolynomialConjugate T S H i = h * B i)
    (Q : Ideal R₀) [Q.IsPrime] (hBQ : ∀ i, B i ∈ Q) :
    ∀ i, linearPolynomialPullback T (W i) ∈ Q := by
  have hA := linearPolynomialConjugate_preserves_primitive_vector T S hTS hST W hW
  have hrep (i) : linearPolynomialPullback T g * linearPolynomialConjugate T S W i = h * B i :=
    (linearPolynomialConjugate_common_scalar_factorization T S H W g hfactor i).symm.trans (hnew i)
  have hAQ := (primitive_vector_common_factor_presentations_prime_membership_iff
    (linearPolynomialConjugate T S W) B hA hB (linearPolynomialPullback T g) h hh hrep Q).mpr hBQ
  exact (ideal_contains_conjugated_vector_iff_contains_source_pullbacks T S hTS W Q).mp hAQ

end DimensionFourDependence
