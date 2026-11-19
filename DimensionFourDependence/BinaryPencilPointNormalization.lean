import DimensionFourDependence.ConstantKernelSourceReduction

/-! # A source point constructs a normalized pair of homogeneous pencil generators -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] {n : ℕ}
local notation "R₀" => MvPolynomial (Fin n) K

/-- At any nonbase source point, an actual inverse binary constant
change produces coprime source generators with values zero and one.
The inverse change simultaneously acts on every binary polynomial,
preserving its original source evaluation exactly. -/
theorem nonbase_source_point_constructs_normalized_homogeneous_binary_pencil
    (p q : R₀) {D : ℕ} (hp : p.IsHomogeneous D) (hq : q.IsHomogeneous D)
    (hrel : IsRelPrime p q) (z : Fin n → K)
    (hz : (![aeval z p, aeval z q] : Fin 2 → K) ≠ 0) :
    ∃ (T S : Matrix (Fin 2) (Fin 2) K) (p' q' : R₀),
      T * S = 1 ∧ S * T = 1 ∧ p'.IsHomogeneous D ∧ q'.IsHomogeneous D ∧
      IsRelPrime p' q' ∧ aeval z p' = 0 ∧ aeval z q' = 1 ∧
      T.map MvPolynomial.C *ᵥ ![p', q'] = ![p, q] ∧
      ∀ F : MvPolynomial (Fin 2) K,
        aeval ![p', q'] (linearPolynomialPullback T F) = aeval ![p, q] F := by
  classical
  obtain ⟨T, S, hTS, hST, hSpoint⟩ := nonzero_vector_constructs_inverse_coordinate_image
    (![aeval z p, aeval z q] : Fin 2 → K) hz 1
  let P : Fin 2 → R₀ := ![p, q]
  let Q : Fin 2 → R₀ := S.map MvPolynomial.C *ᵥ P
  have hTSmap : T.map (MvPolynomial.C : K →+* R₀) * S.map MvPolynomial.C = 1 := by
    rw [← Matrix.map_mul, hTS]
    funext i j
    simp [Matrix.map_apply, Matrix.one_apply]
  have hrestore : T.map MvPolynomial.C *ᵥ Q = P := by
    change T.map MvPolynomial.C *ᵥ (S.map MvPolynomial.C *ᵥ P) = P
    rw [Matrix.mulVec_mulVec, hTSmap, Matrix.one_mulVec]
  have hhom (i : Fin 2) : (Q i).IsHomogeneous D := by
    apply IsHomogeneous.sum
    intro j _
    have hP : (P j).IsHomogeneous D := by fin_cases j <;> assumption
    exact hP.C_mul (S i j)
  have hcoprime : IsRelPrime (Q 0) (Q 1) := by
    intro δ h0 h1
    have hδQ (j : Fin 2) : δ ∣ Q j := by fin_cases j <;> assumption
    have hδP (i : Fin 2) : δ ∣ P i := by
      rw [← hrestore]
      change δ ∣ ∑ j, C (T i j) * Q j
      exact Finset.dvd_sum (fun j _ => dvd_mul_of_dvd_right (hδQ j) _)
    exact hrel (hδP 0) (hδP 1)
  have hvalues : (fun i => aeval z (Q i)) = Pi.single (1 : Fin 2) (1 : K) := by
    have heq : (fun i => aeval z (Q i)) = S *ᵥ ![aeval z p, aeval z q] := by
      funext i
      simp only [Q, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
        map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
      rfl
    exact heq.trans hSpoint
  have hQ : ![Q 0, Q 1] = Q := by funext i; fin_cases i <;> rfl
  refine ⟨T, S, Q 0, Q 1, hTS, hST, hhom 0, hhom 1, hcoprime,
    ?_, ?_, ?_, ?_⟩
  · simpa using congrFun hvalues 0
  · simpa using congrFun hvalues 1
  · rw [hQ]
    exact hrestore
  · intro F
    rw [hQ]
    have hpoint : (fun i => aeval Q (linearPolynomialMap T i)) = P := by
      change (fun i => aeval Q (∑ j, C (T i j) * X j)) = P
      simp only [map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq]
      exact hrestore
    rw [linearPolynomialPullback, comp_aeval_apply, hpoint]

end DimensionFourDependence
