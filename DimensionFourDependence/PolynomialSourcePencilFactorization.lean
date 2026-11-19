import DimensionFourDependence.PrimitiveHomogenizedParameterVector
import DimensionFourDependence.PrimitiveVectorRationalScalar

/-! # A rational projective parametrization constructs an original polynomial factorization -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] {m n : ℕ}

/-- A nonzero finite polynomial vector constructs its exact maximal
homogenizing degree, including a nonzero coefficient at that degree. -/
theorem polynomial_vector_constructs_exact_homogenizing_degree
    (v : Fin m → Polynomial K) (hv : v ≠ 0) :
    ∃ N : ℕ, (∀ i, (v i).natDegree ≤ N) ∧ ∃ i, (v i).coeff N ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hv
  let N := Finset.univ.sup (fun i => (v i).natDegree)
  have hN (j) : (v j).natDegree ≤ N := Finset.le_sup (f := fun i => (v i).natDegree) (Finset.mem_univ j)
  refine ⟨N, hN, ?_⟩
  by_cases hN0 : N = 0
  · refine ⟨i, ?_⟩
    have hiN : (v i).natDegree = N := by have := hN i; omega
    rw [← hiN]
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hi
  · obtain ⟨j, _hj, hNj⟩ := Finset.exists_mem_eq_sup Finset.univ
      ⟨i, Finset.mem_univ i⟩ (fun i => (v i).natDegree)
    refine ⟨j, ?_⟩
    change N = (v j).natDegree at hNj
    have hj : v j ≠ 0 := by
      intro hz
      rw [hz, Polynomial.natDegree_zero] at hNj
      exact hN0 hNj
    rw [hNj]
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hj

local notation "R₀" => MvPolynomial (Fin n) K
local notation "F₀" => FractionRing (MvPolynomial (Fin n) K)

/-- A homogeneous parameter vector has the exact product source
degree after evaluation at two homogeneous forms of the same degree. -/
theorem homogeneous_parameter_value_source_homogeneous
    (v : Polynomial K) (N : ℕ) (p q : R₀) {D : ℕ}
    (hp : p.IsHomogeneous D) (hq : q.IsHomogeneous D) :
    (homogeneousParameterPolynomialValue v N p q).IsHomogeneous (D * N) := by
  apply (Polynomial.isHomogeneous_homogenize v).aeval
  intro i
  fin_cases i
  · exact hp
  · exact hq

variable [IsAlgClosed K]

/-- From an actual rational projective representation over a reduced
source pencil, construct the common original polynomial scalar and
the primitive polynomial vector. All parameter denominators disappear;
the representation is an identity in the original source ring. -/
theorem projective_parameter_representation_constructs_primitive_source_polynomial_factorization
    (H : Fin m → R₀) (p q : R₀) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (v : Fin m → Polynomial K) (hv : v ≠ 0)
    (hprim : ∀ f : Polynomial K, (∀ i, f ∣ v i) → IsUnit f)
    (r : F₀) (hr : r ≠ 0)
    (ht : Transcendental K (algebraMap R₀ F₀ p / algebraMap R₀ F₀ q))
    (hrep : ∀ i, algebraMap R₀ F₀ (H i) =
      r * Polynomial.aeval (algebraMap R₀ F₀ p / algebraMap R₀ F₀ q) (v i)) :
    ∃ (N : ℕ) (g : R₀), (∀ i, (v i).natDegree ≤ N) ∧
      (∃ i, (v i).coeff N ≠ 0) ∧ g ≠ 0 ∧
      IsPrimitiveVec (fun i => homogeneousParameterPolynomialValue (v i) N p q) ∧
      (fun i => homogeneousParameterPolynomialValue (v i) N p q) ≠ 0 ∧
      ∀ i, H i = g * homogeneousParameterPolynomialValue (v i) N p q := by
  obtain ⟨N, hN, htop⟩ := polynomial_vector_constructs_exact_homogenizing_degree v hv
  let W : Fin m → R₀ := fun i => homogeneousParameterPolynomialValue (v i) N p q
  have hWne : W ≠ 0 := homogenized_parameter_vector_nonzero_of_transcendental_ratio v hv hN p q hq ht
  have hWprim : IsPrimitiveVec W :=
    reduced_pencil_homogenized_primitive_parameter_vector_isPrimitive v hprim hN htop p q hrel hWne
  have hqF : algebraMap R₀ F₀ q ≠ 0 :=
    fun h => hq (IsFractionRing.injective R₀ F₀ (h.trans (map_zero _).symm))
  have hqN := pow_ne_zero N hqF
  have hW (i) : algebraMap R₀ F₀ (W i) = algebraMap R₀ F₀ q ^ N *
      Polynomial.aeval (algebraMap R₀ F₀ p / algebraMap R₀ F₀ q) (v i) := by
    change (IsScalarTower.toAlgHom K R₀ F₀) (homogeneousParameterPolynomialValue (v i) N p q) = _
    rw [homogeneousParameterPolynomialValue_algHom]
    exact homogeneousParameterPolynomialValue_fraction (v i) (hN i) _ _ hqF
  have hrepW (i) : algebraMap R₀ F₀ (H i) =
      (r / algebraMap R₀ F₀ q ^ N) * algebraMap R₀ F₀ (W i) := by
    rw [hrep, hW]
    field_simp
  obtain ⟨g, hg, hfactor⟩ := primitive_vector_rational_scalar_constructs_polynomial_factor W H hWprim
    (r / algebraMap R₀ F₀ q ^ N) hrepW
  have hg0 : g ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hg
    exact (div_ne_zero hr hqN) hg.symm
  exact ⟨N, g, hN, htop, hg0, hWprim, hWne, hfactor⟩

end DimensionFourDependence
