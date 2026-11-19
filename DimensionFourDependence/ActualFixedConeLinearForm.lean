import DimensionFourDependence.GaussLinearCoefficientRigidity
import DimensionFourDependence.LinearSourceDenominatorPower

/-! # The polynomial cone covector is a fixed ternary source linear form

The nonconstant scalar member makes the evaluated linear factor an
original source polynomial. Its Euler weight makes it homogeneous linear.
Integral normalization forces the reduced parameter denominator to divide
its power. Homogeneity and the transverse denominator then give q=c y^D
for an actual ternary linear form y. Original transverse independence
identifies every polynomial parameter coefficient with a fixed constant.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)

local notation "R₀" => MvPolynomial (Fin 4) K
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "C₀" => closedGaussParameterField H I
local notation "x₀" => (fun i : Fin 3 => rationalCoordinate (K := K) i.castSucc)

/-- The original homogeneous map's polynomial linear-power data
construct a fixed original ternary linear form, constant parameter
covector coefficients, and the exact denominator power q=c y^D. -/
theorem actual_polynomial_cone_factor_constructs_fixed_ternary_linear_form
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hind : ¬ ComponentsDependent H)
    (e₀ e : RatFunc K ≃ₐ[K] C₀)
    (p q : R₀) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e₀ RatFunc.X =
      algebraMap R₀ S₀ p / algebraMap R₀ S₀ q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3))
    (p' : R₀) (q₀ : MvPolynomial (Fin 3) K) (hq₀ : q₀ ≠ 0) {D : ℕ} (hD : 0 < D)
    (hq'hom : (rename Fin.castSucc q₀).IsHomogeneous D)
    (hrel' : IsRelPrime p' (rename Fin.castSucc q₀))
    (hparameter' : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap R₀ S₀ p' / algebraMap R₀ S₀ (rename Fin.castSucc q₀))
    (v : Fin 3 → Polynomial K) (A : Fin 3 → Polynomial K)
    (hA : ∃ i, 0 < (A i).natDegree)
    (hfirst : ∀ i : Fin 3, algebraMap R₀ S₀ (H i.castSucc) =
      Polynomial.aeval (closedGaussParameterSourceHom H I e RatFunc.X) (A i) *
        (MvPolynomial.eval₂ (Polynomial.aeval
          (closedGaussParameterSourceHom H I e RatFunc.X)).toRingHom x₀
            (polynomialParameterLinearForm v)) ^ d) :
    ∃ c : Fin 3 → K, c ≠ 0 ∧ (∀ i, v i = Polynomial.C (c i)) ∧
      D ≤ d ∧ ∃ γ : K, γ ≠ 0 ∧ q₀ = C γ * linearFormPolynomial c ^ D ∧
        ∀ i : Fin 3, algebraMap R₀ S₀ (H i.castSucc) =
          Polynomial.aeval (closedGaussParameterSourceHom H I e RatFunc.X) (A i) *
            (algebraMap R₀ S₀ (rename Fin.castSucc (linearFormPolynomial c))) ^ d := by
  classical
  let t := closedGaussParameterSourceHom H I e RatFunc.X
  let l : S₀ := MvPolynomial.eval₂ (Polynomial.aeval t).toRingHom x₀ (polynomialParameterLinearForm v)
  have ht : sourceEuler (K := K) t = 0 :=
    closedGaussParameterField_le_sourceEuler_constants H hH I (e RatFunc.X).property
  obtain ⟨k, hk⟩ := hA
  obtain ⟨Z, hZvalue, hZhom, _hZlinear⟩ := polynomial_parameter_linear_value_constructs_source_linear_form
    t ht Fin.castSucc v (A k) hk d (H k.castSucc) (hfirst k)
  have hH0 : H 0 ≠ 0 := (linearIndependent_of_componentsIndependent H hind).ne_zero 0
  have hZ : Z ≠ 0 := by
    intro hz
    apply hH0
    apply IsFractionRing.injective R₀ S₀
    have he := hfirst 0
    rw [← hZvalue, hz, map_zero, zero_pow (Nat.ne_of_gt hd), mul_zero] at he
    simpa only [show (0 : Fin 3).castSucc = (0 : Fin 4) by decide, map_zero] using he
  have hq' : rename Fin.castSucc q₀ ≠ (0 : R₀) := by
    simpa only [map_zero] using (rename_injective Fin.castSucc (Fin.castSucc_injective 3)).ne hq₀
  have hdiv : rename Fin.castSucc q₀ ∣ Z ^ d := by
    apply reduced_parameter_denominator_dvd_source_factor_power (K := K) (F := S₀)
      p' (rename Fin.castSucc q₀) hq' hrel' Z hZ (A k) hk d (H k.castSucc)
    rw [← hparameter', hZvalue]
    exact hfirst k
  obtain ⟨y, hy, hyhom, hrename, hDd, γ, hγ, hqpower⟩ :=
    vertex_independent_denominator_linear_power_constructs_ternary_linear_form
      (rename Fin.castSucc q₀) Z hq' hD hq'hom (transverse_rename_vertex_degree_zero q₀)
      hZ hZhom hdiv
  let c : Fin 3 → K := fun i => (pderiv i y).coeff 0
  have hyform : y = linearFormPolynomial c := eq_sum_of_isHomogeneous_one hyhom
  have hc : c ≠ 0 := by
    intro hz
    apply hy
    rw [hyform, hz]
    simp [linearFormPolynomial]
  have hfixed : l = algebraMap R₀ S₀ (rename Fin.castSucc (linearFormPolynomial c)) := by
    dsimp only [l]
    rw [← hZvalue, ← hrename, hyform]
  have hv := actual_gauss_polynomial_covector_constant_of_fixed_ternary_source_value
    H I e₀ e p q hp0 hq0 hrel hp hq hparameter hvertex v c hfixed
  have hqform : q₀ = C γ * linearFormPolynomial c ^ D := by
    apply rename_injective Fin.castSucc (Fin.castSucc_injective 3)
    rw [map_mul, rename_C, map_pow]
    simpa only [hyform] using hqpower
  refine ⟨c, hc, hv, hDd, γ, hγ, hqform, ?_⟩
  intro i
  rw [hfirst, ← hfixed]

end DimensionFourDependence
