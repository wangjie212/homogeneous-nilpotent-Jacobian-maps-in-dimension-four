import DimensionFourDependence.BinaryAnnihilatorEulerReduction
import DimensionFourDependence.PrimitiveBinaryDirection
import DimensionFourDependence.NilpotentBinaryRadialPair

/-! # The nonzero vertical-derivative branch of Proposition 2.1 in original source coordinates -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- Equal binary homogeneous degrees give the exact Wronskian
annihilation of the original radial pair. -/
theorem binary_homogeneous_wronskian_radial_pairing_zero
    (A B : R₀) {e : ℕ} (hA : A.IsHomogeneous e) (hB : B.IsHomogeneous e)
    (hAz : pderiv 2 A = 0) (hAw : pderiv 3 A = 0)
    (hBz : pderiv 2 B = 0) (hBw : pderiv 3 B = 0) :
    (B * pderiv 0 A - A * pderiv 0 B) * X 0 +
      (B * pderiv 1 A - A * pderiv 1 B) * X 1 = 0 := by
  have ha := hA.sum_X_mul_pderiv
  have hb := hB.sum_X_mul_pderiv
  simp [Fin.sum_univ_succ, hAz, hAw, hBz, hBw, nsmul_eq_mul] at ha hb
  linear_combination B * ha - A * hb

/-- From the original homogeneous nilpotent map and its actual
two-axis polynomial kernel, a nonzero vertical derivative of the first
pair forces that entire pair to vanish. Both mixed trace constraints,
the rational derivative vector, its Euler equations and the polynomial
scaled eigenvector contradiction are constructed internally. -/
theorem nilpotent_two_axis_kernel_nonzero_vertical_pair_zero
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (A B : R₀) {e : ℕ}
    (hA : A.IsHomogeneous e) (hB : B.IsHomogeneous e) (hB0 : B ≠ 0)
    (hAz : pderiv 2 A = 0) (hAw : pderiv 3 A = 0)
    (hBz : pderiv 2 B = 0) (hBw : pderiv 3 B = 0)
    (hWr : (fun i : Fin 2 => B * pderiv (i.castAdd 2) A - A * pderiv (i.castAdd 2) B) ≠ 0)
    (hker : jac H *ᵥ ![0, 0, A, B] = 0)
    (hvertical : ∃ i : Fin 2, pderiv 2 (H (i.castAdd 2)) ≠ 0) :
    H 0 = 0 ∧ H 1 = 0 := by
  let φ := algebraMap R₀ F₀
  let M := (jac H).map φ
  let a : Fin 2 → F₀ := fun i => φ (pderiv (i.castAdd 2) A)
  let b : Fin 2 → F₀ := fun i => φ (pderiv (i.castAdd 2) B)
  let p := φ A
  let q := φ B
  let W : Fin 2 → F₀ := fun i => q * a i - p * b i
  let x : Fin 2 → F₀ := fun i => φ (X (i.castAdd 2))
  let U : Fin 2 → F₀ := fun i => φ (H (i.castAdd 2))
  have hcast0 : (0 : Fin 2).castAdd 2 = (0 : Fin 4) := by decide
  have hcast1 : (1 : Fin 2).castAdd 2 = (1 : Fin 4) := by decide
  have hφ : Function.Injective φ := IsFractionRing.injective R₀ F₀
  have hq : q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hB0)
  have hW (i : Fin 2) : W i = φ (B * pderiv (i.castAdd 2) A - A * pderiv (i.castAdd 2) B) := by
    simp only [W, a, b, p, q, map_sub, map_mul]
  have hW0 : W ≠ 0 := by
    intro hz
    apply hWr
    funext i
    apply hφ
    have he := congrFun hz i
    simpa only [hW, Pi.zero_apply, map_zero] using he
  have hju : (jac (![0, 0, A, B] : Fin 4 → R₀)).map φ = twoAxisDirectionJacobian a b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [jac, twoAxisDirectionJacobian, a, b, hAz, hAw, hBz, hBw]
  have htrace := invariant_polynomial_direction_constructs_two_nilpotent_trace_constraints
    H ![0, 0, A, B] hN hker
  have ht1 : Matrix.trace (M * twoAxisDirectionJacobian a b) = 0 := by
    have he := congrArg φ htrace.1
    simpa only [AddMonoidHom.map_trace, Matrix.map_mul, hju, map_zero] using he
  have ht2 : Matrix.trace (M ^ 2 * twoAxisDirectionJacobian a b) = 0 := by
    have he := congrArg φ htrace.2
    simpa only [AddMonoidHom.map_trace, Matrix.map_mul, Matrix.map_pow, hju, map_zero] using he
  have hkernel (i : Fin 4) : p * M i 2 + q * M i 3 = 0 := by
    have he := congrArg φ (congrFun hker i)
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, jac, map_add, map_mul] at he
    change p * M i 2 + q * M i 3 = 0
    simpa only [p, q, M, jac, Matrix.of_apply, Matrix.map_apply, mul_comm] using he
  obtain ⟨v, hcol2, hcol3, hbv, hbMv⟩ :=
    two_axis_kernel_traces_construct_binary_derivative_constraints M a b p q hq hkernel ht1 ht2
  have hv : (fun i : Fin 2 => v (i.castAdd 2)) ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := hvertical
    apply hi
    apply hφ
    have he := hcol2 (i.castAdd 2)
    rw [congrFun hz i] at he
    simp only [Pi.zero_apply, mul_zero] at he
    simpa only [M, jac, Matrix.of_apply, Matrix.map_apply, map_zero] using he
  have hbx : W 0 * x 0 + W 1 * x 1 = 0 := by
    have he := congrArg φ (binary_homogeneous_wronskian_radial_pairing_zero A B hA hB hAz hAw hBz hBw)
    simpa only [hW, x, hcast0, hcast1, map_add, map_mul, map_zero] using he
  have hx : x 0 ≠ 0 := by
    intro hz
    change φ (X (0 : Fin 4)) = 0 at hz
    exact MvPolynomial.X_ne_zero (R := K) (0 : Fin 4) (hφ (by simpa only [map_zero] using hz))
  have hEuler (i : Fin 2) : (d : F₀) * U i = x 0 * M (i.castAdd 2) 0 +
      x 1 * M (i.castAdd 2) 1 + φ (X 2) * M (i.castAdd 2) 2 + φ (X 3) * M (i.castAdd 2) 3 := by
    have he := congrArg φ (hH (i.castAdd 2)).sum_X_mul_pderiv
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, nsmul_eq_mul,
      map_add, map_mul, map_natCast] at he
    change _ = (d : F₀) * U i at he
    change φ (X 0) * φ (pderiv 0 (H (i.castAdd 2))) +
      (φ (X 1) * φ (pderiv 1 (H (i.castAdd 2))) +
      (φ (X 2) * φ (pderiv 2 (H (i.castAdd 2))) +
      φ (X 3) * φ (pderiv 3 (H (i.castAdd 2))))) = (d : F₀) * U i at he
    change (d : F₀) * U i = _
    dsimp only [x, M, jac, Matrix.of_apply, Matrix.map_apply]
    simp only [hcast0, hcast1]
    linear_combination -he
  have hcross := binary_trace_constraints_and_euler_force_radial_outputs M W x U v
    q p (φ (X 2)) (φ (X 3)) (d : F₀) hW0 hx (Nat.cast_ne_zero.mpr hd.ne')
    hv hcol2 hcol3 hbx hbv hbMv hEuler
  apply nilpotent_binary_radial_output_pair_zero H hN
  apply hφ
  simpa only [map_mul, x, U, hcast0, hcast1] using hcross

end DimensionFourDependence
