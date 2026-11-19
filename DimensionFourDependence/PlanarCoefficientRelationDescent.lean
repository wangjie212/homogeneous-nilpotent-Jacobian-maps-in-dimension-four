import DimensionFourDependence.PlanarActiveFractionFieldDependence
import DimensionFourDependence.PlanarGroupedHomogeneousCoefficients

/-! # A shared active monomial gives a homogeneous coefficient relation over the actual base -/

namespace DimensionFourDependence.Shear

open MvPolynomial

set_option maxHeartbeats 1100000

section FieldPair

variable {F σ : Type*} [Field F]

/-- In a nonzero dependent pair, the coefficient of any shared
nonzero monomial gives the exact ratio. -/
theorem dependent_nonzero_pair_cross_mul_of_coefficient
    (p q : MvPolynomial σ F) (hp : p ≠ 0) (hq : q ≠ 0)
    (hd : ComponentsDependent (![p,q] : Fin 2 → MvPolynomial σ F))
    (m : σ →₀ ℕ) (hm : p.coeff m ≠ 0) :
    q.coeff m ≠ 0 ∧ C (q.coeff m) * p = C (p.coeff m) * q := by
  obtain ⟨c, hc, hrel⟩ := hd
  have h₀ : C (c 0) * p + C (c 1) * q = 0 := by
    simpa [Fin.sum_univ_two, MvPolynomial.smul_eq_C_mul] using hrel
  have hne₀ : c 0 ≠ 0 := by
    intro hz
    have hz' : C (c 1) * q = 0 := by simpa [hz] using h₀
    have h1 : c 1 = 0 := C_injective σ F
      (((mul_eq_zero.mp hz').resolve_right hq).trans (map_zero _).symm)
    apply hc
    funext i
    fin_cases i
    · exact hz
    · exact h1
  have hne₁ : c 1 ≠ 0 := by
    intro hz
    have hz' : C (c 0) * p = 0 := by simpa [hz] using h₀
    apply (C_ne_zero.mpr hne₀)
    exact (mul_eq_zero.mp hz').resolve_right hp
  have hscalar : c 0 * p.coeff m + c 1 * q.coeff m = 0 := by
    simpa only [MvPolynomial.coeff_add, coeff_C_mul, MvPolynomial.coeff_zero, Finsupp.zero_apply] using
      congrArg (fun f : MvPolynomial σ F => f.coeff m) h₀
  refine ⟨?_, ?_⟩
  · intro hz
    rw [hz, mul_zero, add_zero] at hscalar
    exact hm ((mul_eq_zero.mp hscalar).resolve_left hne₀)
  · have hp₀ : C (c 0) * p = -(C (c 1) * q) := eq_neg_of_add_eq_zero_left h₀
    have hc₀ : (C (c 0) : MvPolynomial σ F) * C (p.coeff m) = -(C (c 1) * C (q.coeff m)) := by
      simp only [← map_mul, ← map_neg]
      rw [eq_neg_of_add_eq_zero_left hscalar]
    apply mul_left_cancel₀ (C_ne_zero.mpr hne₁)
    linear_combination p * hc₀ - C (p.coeff m) * hp₀

end FieldPair

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "L" => FractionRing R₂
local notation "A₂" => MvPolynomial (Fin 2) R₂
local notation "Aₗ" => MvPolynomial (Fin 2) L

/-- The actual original normalized nonzero pair constructs a common
active coefficient and an exact relation over the polynomial base.
The two coefficients have the same homogeneous degree. -/
theorem normalized_planar_pair_constructs_homogeneous_coefficient_relation
    (A : Fin 2 → R₄) {d : ℕ} (hA : ∀ i, (A i).IsHomogeneous d)
    (hN : IsNilpotent (planarActiveJacobian A))
    (h0 : planarActiveNormalized (A 0) ≠ 0) (h1 : planarActiveNormalized (A 1) ≠ 0) :
    ∃ (k : ℕ) (a b : R₂), a ≠ 0 ∧ b ≠ 0 ∧ a.IsHomogeneous k ∧ b.IsHomogeneous k ∧
      base4 a * planarActiveNormalized (A 0) + base4 b * planarActiveNormalized (A 1) = 0 := by
  classical
  let U := planarActiveNormalized (A 0)
  let V := planarActiveNormalized (A 1)
  let p : A₂ := planarCoefficientEquiv U
  let q : A₂ := planarCoefficientEquiv V
  have hp : p ≠ 0 := fun h => h0 (planarCoefficientEquiv.injective (h.trans (map_zero _).symm))
  obtain ⟨m, hm⟩ := support_nonempty.mpr hp
  have hm' : p.coeff m ≠ 0 := mem_support_iff.mp hm
  let j := algebraMap R₂ L
  let P : Aₗ := MvPolynomial.map j p
  let Q : Aₗ := MvPolynomial.map j q
  have hinj : Function.Injective j := IsFractionRing.injective R₂ L
  have hP : P ≠ 0 := fun h => h0 (activeFractionPolynomial_injective (h.trans (map_zero _).symm))
  have hQ : Q ≠ 0 := fun h => h1 (activeFractionPolynomial_injective (h.trans (map_zero _).symm))
  have hd : ComponentsDependent (![P,Q] : Fin 2 → Aₗ) := by
    have h := planar_normalized_active_block_componentsDependent_over_fraction_field A hN
    have hEq : (fun i : Fin 2 => activeFractionPolynomial (planarActiveNormalized (A i))) = ![P,Q] := by
      funext i
      fin_cases i <;> rfl
    rwa [← hEq]
  have hPm : P.coeff m ≠ 0 := by
    change (MvPolynomial.map j p).coeff m ≠ 0
    rw [coeff_map]
    exact fun h => hm' (hinj (h.trans (map_zero _).symm))
  obtain ⟨hqne, hcross⟩ := dependent_nonzero_pair_cross_mul_of_coefficient P Q hP hQ hd m hPm
  have hq' : q.coeff m ≠ 0 := by
    intro hz
    apply hqne
    change (MvPolynomial.map j q).coeff m = 0
    rw [coeff_map, hz, map_zero]
  have hpoly : C (q.coeff m) * p = C (p.coeff m) * q := by
    apply MvPolynomial.map_injective j hinj
    simp only [map_mul, MvPolynomial.map_C]
    simpa only [P, Q, coeff_map] using hcross
  have hU := homogeneous_planarCoefficientEquiv_coeff U (planarActiveNormalized_isHomogeneous _ (hA 0)) m
  have hV := homogeneous_planarCoefficientEquiv_coeff V (planarActiveNormalized_isHomogeneous _ (hA 1)) m
  refine ⟨d - m.degree, q.coeff m, -(p.coeff m), hq', neg_ne_zero.mpr hm', hV, hU.neg, ?_⟩
  apply (planarCoefficientEquiv (K := K)).injective
  simp only [map_add, map_mul, map_zero, planarCoefficientEquiv_base4, map_neg]
  change C (q.coeff m) * p + -C (p.coeff m) * q = 0
  linear_combination hpoly

end DimensionFourDependence.Shear
