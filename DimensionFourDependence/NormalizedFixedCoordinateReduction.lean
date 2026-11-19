import DimensionFourDependence.FixedCoordinateReduction
import DimensionFourDependence.LastCoordinateDehomogenization

/-! # Section 6.2: normalized nilpotent dehomogenization over the original field -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K] {n : ℕ}

/-- The active origin values of the actual final-coordinate chart. -/
noncomputable def fixedCoordinateChartConstants
    (B : Fin n → MvPolynomial (Fin (n + 1)) K) : Fin n → K :=
  fun i => aeval (fun _ : Fin n => (0 : K)) (lastCoordinateDehomogenize (B i))

/-- The normalized dehomogenized perturbation in its own active
polynomial ring, after removing the actual active-origin value. -/
noncomputable def normalizedFixedCoordinateChart
    (B : Fin n → MvPolynomial (Fin (n + 1)) K) : Fin n → MvPolynomial (Fin n) K :=
  fun i => lastCoordinateDehomogenize (B i) - C (fixedCoordinateChartConstants B i)

/-- The chart Jacobian is precisely the dehomogenized leading block
of the full perturbation Jacobian. -/
theorem lastCoordinateDehomogenize_leading_jacobian
    (B : Fin n → MvPolynomial (Fin (n + 1)) K) :
    jac (fun i => lastCoordinateDehomogenize (B i)) =
      ((jac (Fin.lastCases 0 B)).submatrix Fin.castSucc Fin.castSucc).map
        (lastCoordinateDehomogenize (K := K) (n := n)) := by
  funext i j
  change pderiv j (lastCoordinateDehomogenize (B i)) =
    lastCoordinateDehomogenize (pderiv j.castSucc (Fin.lastCases 0 B i.castSucc))
  rw [Fin.lastCases_castSucc, lastCoordinateDehomogenize_pderiv]

/-- Subtracting target constants leaves the actual Jacobian unchanged. -/
theorem jacobian_subtract_constant_outputs
    (b : Fin n → MvPolynomial (Fin n) K) (c : Fin n → K) :
    jac (fun i => b i - C (c i)) = jac b := by
  ext i j
  simp [jac]

/-- The normalized chart has the same active Jacobian as the raw chart. -/
theorem normalizedFixedCoordinateChart_jacobian
    (B : Fin n → MvPolynomial (Fin (n + 1)) K) :
    jac (normalizedFixedCoordinateChart B) =
      ((jac (Fin.lastCases 0 B)).submatrix Fin.castSucc Fin.castSucc).map
        (lastCoordinateDehomogenize (K := K) (n := n)) := by
  change jac (fun i => lastCoordinateDehomogenize (B i) -
    C (fixedCoordinateChartConstants B i)) = _
  rw [jacobian_subtract_constant_outputs, lastCoordinateDehomogenize_leading_jacobian]

/-- Nilpotence descends to the actual active polynomial ring. This
is specialization of a genuine polynomial matrix, with no rational
coordinate change over a parameter field. -/
theorem normalizedFixedCoordinateChart_nilpotent
    (B : Fin n → MvPolynomial (Fin (n + 1)) K)
    (hN : IsNilpotent ((jac (Fin.lastCases 0 B)).submatrix Fin.castSucc Fin.castSucc)) :
    IsNilpotent (jac (normalizedFixedCoordinateChart B)) := by
  rw [normalizedFixedCoordinateChart_jacobian]
  exact hN.map (lastCoordinateDehomogenize (K := K) (n := n)).toRingHom.mapMatrix

/-- The actual chart normalization vanishes at its own origin. -/
theorem normalizedFixedCoordinateChart_origin
    (B : Fin n → MvPolynomial (Fin (n + 1)) K) (i : Fin n) :
    aeval (fun _ : Fin n => (0 : K)) (normalizedFixedCoordinateChart B i) = 0 := by
  simp [normalizedFixedCoordinateChart, fixedCoordinateChartConstants]

/-- The chart degree bound and exact homogeneous reconstruction retain
the constant translation that was removed during normalization. -/
theorem normalizedFixedCoordinateChart_homogeneous_reconstruction
    (B : Fin n → MvPolynomial (Fin (n + 1)) K) {d : ℕ}
    (hB : ∀ i, (B i).IsHomogeneous d) (i : Fin n) :
    (normalizedFixedCoordinateChart B i).totalDegree ≤ d ∧
      B i = lastCoordinateHomogenize (normalizedFixedCoordinateChart B i) d +
        C (fixedCoordinateChartConstants B i) * X (Fin.last n) ^ d := by
  have h := homogeneous_form_reconstructs_normalized_final_coordinate_chart (B i) (hB i)
  exact ⟨h.1, h.2.2⟩

variable [CharZero K]

/-- The original homogeneous nilpotent map constructs every datum in
Section 6.2: inverse constant coordinates, a fixed final coordinate,
the normalized ternary perturbation, its degree bound, and its actual
nilpotent Jacobian, together with exact reconstruction of all outputs. -/
theorem original_homogeneous_nilpotent_map_constructs_normalized_fixed_coordinate_chart
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ}
    (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H)) :
    ∃ (T S : Matrix (Fin 4) (Fin 4) K)
      (B : Fin 3 → MvPolynomial (Fin 4) K),
      T * S = 1 ∧ S * T = 1 ∧
      linearPolynomialConjugate T S H = Fin.lastCases 0 B ∧
      (∀ i, (B i).IsHomogeneous d) ∧
      (∀ i, (normalizedFixedCoordinateChart B i).totalDegree ≤ d) ∧
      (∀ i, aeval (fun _ : Fin 3 => (0 : K)) (normalizedFixedCoordinateChart B i) = 0) ∧
      IsNilpotent (jac (normalizedFixedCoordinateChart B)) ∧
      ∀ i, B i = lastCoordinateHomogenize (normalizedFixedCoordinateChart B i) d +
        C (fixedCoordinateChartConstants B i) * X (Fin.last 3) ^ d := by
  obtain ⟨T, S, B, hTS, hST, hG, hB, hn⟩ :=
    original_homogeneous_nilpotent_map_constructs_fixed_coordinate_reduction H hd hH hN
  refine ⟨T, S, B, hTS, hST, hG, hB, ?_,
    normalizedFixedCoordinateChart_origin B,
    normalizedFixedCoordinateChart_nilpotent B hn, ?_⟩
  · exact fun i => (normalizedFixedCoordinateChart_homogeneous_reconstruction B hB i).1
  · exact fun i => (normalizedFixedCoordinateChart_homogeneous_reconstruction B hB i).2

end DimensionFourDependence
