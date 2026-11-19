import DimensionFourDependence.PlanarCoefficientRelationDescent
import DimensionFourDependence.CompleteIntersectionPair
import DimensionFourDependence.LinearBaseShearFrame
import DimensionFourDependence.Homogeneous

/-! # Extracting the primitive homogeneous coefficient pair and common scalar in Proposition 6.3 -/

namespace DimensionFourDependence.Shear

open MvPolynomial Matrix

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "A₂" => MvPolynomial (Fin 2) R₂

theorem base4_injective : Function.Injective (base4 (K := K)) := by
  intro a b h
  apply C_injective (Fin 2) R₂
  have he := congrArg (planarCoefficientEquiv (K := K)) h
  simpa only [planarCoefficientEquiv_base4] using he

theorem base4_mul (a b : R₂) : base4 (a * b) = base4 a * base4 b := map_mul (aeval ![X 2,X 3]) a b

theorem base4_isRelPrime (a b : R₂) (ha : a ≠ 0) (hc : IsRelPrime a b) :
    IsRelPrime (base4 a) (base4 b) := by
  intro s hsa hsb
  let E := planarCoefficientEquiv (K := K)
  have hE (p : R₂) : E (base4 p) = (C p : A₂) := planarCoefficientEquiv_base4 p
  obtain ⟨c, hac⟩ := hsa
  have hC : (C a : A₂) = E s * E c := by
    have h := congrArg E hac
    simpa only [hE, map_mul] using h
  have hs : E s ≠ 0 := left_ne_zero_of_mul (hC ▸ C_ne_zero.mpr ha)
  have ht : E c ≠ 0 := right_ne_zero_of_mul (hC ▸ C_ne_zero.mpr ha)
  have hd : (E s).totalDegree = 0 := by
    have h := congrArg totalDegree hC
    rw [totalDegree_C, totalDegree_mul_of_isDomain hs ht] at h
    omega
  have hscalar := totalDegree_eq_zero_iff_eq_C.mp hd
  have hdiv (p : R₂) (hp : s ∣ base4 p) : (E s).coeff 0 ∣ p := by
    obtain ⟨w, hw⟩ := hp
    have hEOS : (C p : A₂) = E s * E w := by
      simpa only [hE, map_mul] using congrArg E hw
    refine ⟨(E w).coeff 0, ?_⟩
    have h := congrArg (constantCoeff : A₂ →+* R₂) hEOS
    rw [constantCoeff_C, map_mul] at h
    exact h
  have hunit : IsUnit (E s) := by
    rw [hscalar]
    exact (hc (hdiv a ⟨c,hac⟩) (hdiv b hsb)).map C
  have he : IsUnit (E.symm (E s)) := hunit.map E.symm.toRingHom
  rwa [E.symm_apply_apply] at he

theorem base4_isHomogeneous (a : R₂) {r : ℕ} (ha : a.IsHomogeneous r) : (base4 a).IsHomogeneous r := by
  rw [base4_eq_rename]
  exact ha.rename_isHomogeneous

variable [CharZero K]

/-- The nonzero active pair constructs relatively prime homogeneous
coefficients and a single nonzero homogeneous polynomial multiplier. -/
theorem normalized_planar_pair_constructs_primitive_shear_factor
    (A : Fin 2 → R₄) {d : ℕ} (hA : ∀ i, (A i).IsHomogeneous d)
    (hN : IsNilpotent (planarActiveJacobian A))
    (h0 : planarActiveNormalized (A 0) ≠ 0) (h1 : planarActiveNormalized (A 1) ≠ 0) :
    ∃ (r : ℕ) (a b : R₂) (q : R₄),
      r ≤ d ∧ a ≠ 0 ∧ b ≠ 0 ∧ q ≠ 0 ∧ IsRelPrime a b ∧
      a.IsHomogeneous r ∧ b.IsHomogeneous r ∧ q.IsHomogeneous (d-r) ∧
      planarActiveNormalized (A 0) = base4 b * q ∧
      planarActiveNormalized (A 1) = -base4 a * q := by
  obtain ⟨k, a₀, b₀, ha₀, hb₀, ha₀H, hb₀H, hr⟩ :=
    normalized_planar_pair_constructs_homogeneous_coefficient_relation A hA hN h0 h1
  have hv : (![a₀,b₀] : Fin 2 → R₂) ≠ 0 := by
    intro h
    exact ha₀ (congrFun h 0)
  obtain ⟨g, c, e, _he, hg, _hgH, hH, hprim, hc⟩ :=
    exists_primitive_factorization k ![a₀,b₀] (by intro i; fin_cases i <;> assumption) hv
  let a := c 0
  let b := c 1
  have haeq : a₀ = g * a := congrFun hc 0
  have hbeq : b₀ = g * b := congrFun hc 1
  have ha : a ≠ 0 := fun hz => ha₀ (by rw [haeq, hz, mul_zero])
  have hb : b ≠ 0 := fun hz => hb₀ (by rw [hbeq, hz, mul_zero])
  have hcop : IsRelPrime a b := by
    intro t hta htb
    apply hprim t
    intro i
    fin_cases i <;> assumption
  let r := k - e
  have haH : a.IsHomogeneous r := hH 0
  have hbH : b.IsHomogeneous r := hH 1
  have hbase (p : R₂) (hp : p ≠ 0) : base4 p ≠ 0 := by
    intro hz
    exact hp (base4_injective (hz.trans (map_zero (aeval ![X 2,X 3])).symm))
  have hrel : base4 a * planarActiveNormalized (A 0) + base4 b * planarActiveNormalized (A 1) = 0 := by
    rw [haeq, hbeq, base4_mul, base4_mul] at hr
    apply (mul_eq_zero.mp (show base4 g * _ = 0 from ?_)).resolve_left (hbase g hg)
    linear_combination hr
  obtain ⟨q, hq0, hq1⟩ := relPrime_pair_syzygy (base4 a) (base4 b) (hbase a ha)
    (base4_isRelPrime a b ha hcop) _ _ hrel
  have hq : q ≠ 0 := fun hz => h0 (by rw [hq0, hz, mul_zero])
  have hd' := (planarActiveNormalized_isHomogeneous _ (hA 0)).totalDegree h0
  rw [hq0, totalDegree_mul_of_isDomain (hbase b hb) hq,
    (base4_isHomogeneous b hbH).totalDegree (hbase b hb)] at hd'
  have hr : r ≤ d := by omega
  have hqH : q.IsHomogeneous (d-r) := by
    apply homogeneous_factor_of_product (hbase b hb) (base4_isHomogeneous b hbH)
    rw [← hq0, Nat.add_sub_of_le hr]
    exact planarActiveNormalized_isHomogeneous _ (hA 0)
  exact ⟨r, a, b, q, hr, ha, hb, hq, hcop, haH, hbH, hqH, hq0, hq1⟩

end DimensionFourDependence.Shear
