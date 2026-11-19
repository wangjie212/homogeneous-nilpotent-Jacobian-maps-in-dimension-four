import DimensionFourDependence.VertexLinePrimeIdentification
import DimensionFourDependence.IndependentVectorCoordinateColumns
import DimensionFourDependence.FixedCovectorCoordinateChoice

/-! # Height-two source primes contain at most two independent constant linear forms -/

namespace DimensionFourDependence

open Matrix MvPolynomial Module

set_option maxHeartbeats 3500000

variable {K : Type*} [Field K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- Three independent original constant covectors cannot all give
linear forms in a source prime of height at most two. Actual inverse
coordinates reduce the assertion to the three transverse coordinates. -/
theorem height_le_two_prime_excludes_three_independent_constant_linear_forms
    (Q : Ideal R₀) [Q.IsPrime] (hQ : Q.height ≤ 2)
    (v : Fin 3 → (Fin 4 → K)) (hv : LinearIndependent K v)
    (hmem : ∀ i, linearFormPolynomial (v i) ∈ Q) : False := by
  let e : Fin 3 ↪ Fin 4 := ⟨Fin.castSucc, Fin.castSucc_injective 3⟩
  obtain ⟨A, B, hAB, hBA, hcol⟩ := independent_vector_family_constructs_inverse_coordinate_columns v hv e
  have hTS : Bᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one]
  have hST : Aᵀ * Bᵀ = 1 := by rw [← Matrix.transpose_mul, hBA, Matrix.transpose_one]
  let φ := matrixPolynomialCoordinateEquiv Bᵀ Aᵀ hTS hST
  let P := Q.map φ.toRingHom
  let : P.IsPrime := Ideal.map_isPrime_of_equiv φ
  have hheight : P.height ≤ 2 := by
    have he : P.height = Q.height := φ.toRingEquiv.height_map Q
    exact he.trans_le hQ
  have hform (j : Fin 3) : φ (linearFormPolynomial (v j)) = X j.castSucc := by
    rw [matrixPolynomialCoordinateEquiv_apply, linearPolynomialPullback_linear_form]
    have hr : (fun k => ∑ i, v j i * Bᵀ i k) = Pi.single j.castSucc 1 := by
      funext k
      have he := congrFun (congrFun hBA k) j.castSucc
      have hc (i) : A i j.castSucc = v j i := hcol j i
      simpa only [Matrix.mul_apply, hc, Matrix.transpose_apply, Matrix.one_apply,
        Pi.single_apply, mul_comm, eq_comm] using he
    rw [hr]
    simp [linearFormPolynomial, Pi.single_apply]
  have hcoords (j : Fin 3) : X j.castSucc ∈ P := by
    rw [← hform j]
    exact Ideal.mem_map_of_mem φ.toRingHom (hmem j)
  obtain ⟨j, hj⟩ := height_le_two_prime_has_transverse_coordinate P hheight
  exact hj (hcoords j)

/-- The exact linear map from original constant covectors to source
linear polynomials. -/
noncomputable def sourceConstantLinearFormMap : (Fin 4 → K) →ₗ[K] R₀ :=
  Fintype.linearCombination K (fun i => X i)

theorem sourceConstantLinearFormMap_apply (w : Fin 4 → K) :
    sourceConstantLinearFormMap w = linearFormPolynomial w := by
  simp only [sourceConstantLinearFormMap, Fintype.linearCombination_apply, linearFormPolynomial, smul_eq_C_mul]

/-- The actual subspace of original constant covectors whose linear
polynomials belong to the specified original source ideal. -/
noncomputable def idealConstantCovectorSpace (Q : Ideal R₀) : Submodule K (Fin 4 → K) :=
  (Q.restrictScalars K).comap sourceConstantLinearFormMap

theorem mem_idealConstantCovectorSpace_iff (Q : Ideal R₀) (w : Fin 4 → K) :
    w ∈ idealConstantCovectorSpace Q ↔ linearFormPolynomial w ∈ Q := by
  change sourceConstantLinearFormMap w ∈ Q ↔ _
  rw [sourceConstantLinearFormMap_apply]

/-- The entire actual original constant-linear-form space of a
height-at-most-two prime has dimension at most two. -/
theorem height_le_two_prime_constant_covector_space_finrank_le_two
    (Q : Ideal R₀) [Q.IsPrime] (hQ : Q.height ≤ 2) :
    finrank K (idealConstantCovectorSpace Q) ≤ 2 := by
  by_contra hn
  have hge : 3 ≤ finrank K (idealConstantCovectorSpace Q) := by omega
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hge
  have hv' : LinearIndependent K (fun i : Fin 3 => (v i : Fin 4 → K)) :=
    hv.map' (idealConstantCovectorSpace Q).subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  exact height_le_two_prime_excludes_three_independent_constant_linear_forms Q hQ _ hv'
    (fun i => (mem_idealConstantCovectorSpace_iff Q (v i)).mp (v i).property)

end DimensionFourDependence
