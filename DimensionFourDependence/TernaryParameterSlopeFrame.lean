import DimensionFourDependence.TernaryParameterTraceMinors
import DimensionFourDependence.RationalParameterConstants
import DimensionFourDependence.TernaryGraphPairIndependence

/-! # The rational slope and transverse coordinate of the dependent-pair chart -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2450000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)
local notation "D₀" => (rationalPartial (K := K) (n := 3))
local notation "x₀" => (rationalCoordinate (K := K) (n := 3))

/-- Independence of ordinary polynomials makes their rational ratio
have nonzero rational derivative. -/
theorem rational_ratio_of_independent_polynomials_derivative_ne_zero
    (p q : Polynomial K)
    (hind : ∀ a b : K, Polynomial.C a * p + Polynomial.C b * q = 0 → a = 0 ∧ b = 0) :
    let j := algebraMap (Polynomial K) (RatFunc K)
    j p ≠ 0 ∧ rationalParameterDerivative K (j q / j p) ≠ 0 := by
  let j := algebraMap (Polynomial K) (RatFunc K)
  have hp : p ≠ 0 := by
    intro h
    exact one_ne_zero ((hind 1 0 (by simp [h])).1)
  have hj : Function.Injective j := IsFractionRing.injective _ _
  have hjp : j p ≠ 0 := by simpa only [map_zero] using hj.ne hp
  refine ⟨hjp, ?_⟩
  intro he
  obtain ⟨c, hc⟩ := (rationalParameterDerivative_eq_zero_iff_scalar _).mp he
  have hq := (div_eq_iff hjp).mp hc
  have hz : Polynomial.C (-c) * p + Polynomial.C 1 * q = 0 := by
    apply hj
    simp only [map_add, map_mul, map_zero, map_one, one_mul]
    have hscalar : j (Polynomial.C (-c)) = algebraMap K (RatFunc K) (-c) :=
      (IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K) (-c)).symm
    rw [hscalar, hq, map_neg, neg_mul, neg_add_cancel]
  exact one_ne_zero ((hind (-c) 1 hz).2)

omit [CharZero K] in
/-- In the actual rational source, the reduced trace and minor are
equivalent to the two tangency equations of a normalized derivation. -/
theorem ternary_parameter_normalized_derivation_tangent
    (r v U V : F) (hU : U ≠ 0) (hr : D₀ 1 r ≠ 0)
    (ht : U * D₀ 0 r + V * D₀ 2 r + D₀ 1 v = 0)
    (hm : (U * D₀ 0 r + V * D₀ 2 r) * D₀ 1 v -
      D₀ 1 r * (U * D₀ 0 v + V * D₀ 2 v) = 0) :
    let a := V / U
    let c := D₀ 1 v / (U * D₀ 1 r)
    let Δ := D₀ 0 + c • D₀ 1 + a • D₀ 2
    Δ r = 0 ∧ Δ v = 0 ∧ Δ (x₀ 0) = 1 ∧ Δ (x₀ 1) = c ∧ Δ (x₀ 2) = a := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Derivation.add_apply, Derivation.smul_apply, smul_eq_mul]
    field_simp
    linear_combination ht
  · simp only [Derivation.add_apply, Derivation.smul_apply, smul_eq_mul]
    field_simp
    linear_combination D₀ 1 v * ht - hm
  all_goals simp [Derivation.smul_apply, rationalPartial_coordinate, smul_eq_mul]

/-- The rational transverse coordinate `z - a(r)x` gives an
independent frame together with `x` and the common parameter. -/
theorem ternary_parameter_transverse_frame_independent
    (r a a' : F) (hr : D₀ 1 r ≠ 0) (ha : ∀ i, D₀ i a = a' * D₀ i r) :
    AlgebraicIndependent K (![x₀ 0, r, x₀ 2 - a * x₀ 0] : Fin 3 → F) := by
  let Y : Fin 3 → F := ![x₀ 0, r, x₀ 2 - a * x₀ 0]
  let L : Matrix (Fin 3) (Fin 3) F := of ![![1, 0, 0], (fun i => D₀ i r),
    ![-a - a' * D₀ 0 r * x₀ 0, -(a' * D₀ 1 r * x₀ 0), 1 - a' * D₀ 2 r * x₀ 0]]
  have hJ : rationalJacobian Y = L := by
    funext i j
    change D₀ j (Y i) = L i j
    fin_cases i <;> fin_cases j <;>
      simp [Y, L, Derivation.leibniz, ha, rationalPartial_coordinate, smul_eq_mul] <;> ring
  have hdet : L.det = D₀ 1 r := by
    rw [Matrix.det_fin_three]
    simp [L]
    ring
  apply rationalJacobian_full_row_rank_algebraicIndependent Y
  rw [hJ]
  have hd : L.det ≠ 0 := hdet.symm ▸ hr
  rw [Matrix.rank_of_det_ne_zero hd, Fintype.card_fin]

end DimensionFourDependence
