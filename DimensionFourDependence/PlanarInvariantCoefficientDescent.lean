import DimensionFourDependence.CoprimeFractionCoefficientDescent
import DimensionFourDependence.PlanarShearInvariantFractionPolynomial

/-! # Both axis specializations force every coefficient of the invariant polynomial to descend -/

namespace DimensionFourDependence.Shear

open MvPolynomial

set_option maxHeartbeats 1600000

section AxisEvaluation

variable {R F σ : Type*} [CommRing R] [CommRing F]

theorem polynomial_axis_evaluation_map_coefficients (φ : R →+* F)
    (v : σ → Polynomial R) (p : MvPolynomial σ R) :
    aeval (fun i => (v i).map φ) (MvPolynomial.map φ p) = (aeval v p).map φ := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, MvPolynomial.map_X, aeval_X, Polynomial.map_mul, hp]

end AxisEvaluation

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "A₂" => MvPolynomial (Fin 2) R₂
local notation "L" => FractionRing R₂
local notation "Aₗ" => MvPolynomial (Fin 2) L
local notation "ι" => (algebraMap R₂ L)

/-- Any axis on which the linear invariant becomes a scalar times
the axis coordinate supplies that scalar power times every coefficient
as an actual element of the base ring. -/
theorem invariant_parameter_coeff_mul_is_base_on_axis
    (S : Aₗ) (q : A₂) (f : Polynomial L)
    (hv : MvPolynomial.map ι q = Polynomial.aeval S f)
    (s : Fin 2 → Polynomial R₂) (a : R₂)
    (hs : aeval (fun i => (s i).map ι) S = Polynomial.C (ι a) * Polynomial.X)
    (j : ℕ) : ι ((aeval s q).coeff j) = ι (a ^ j) * f.coeff j := by
  let E : Aₗ →ₐ[L] Polynomial L := aeval (fun i => (s i).map ι)
  have he := (polynomial_axis_evaluation_map_coefficients ι s q).symm
  change (aeval s q).map ι = E (MvPolynomial.map ι q) at he
  rw [hv, ← Polynomial.aeval_algHom_apply, show E S = _ from hs] at he
  have he' : (aeval s q).map ι = f.comp (Polynomial.C (ι a) * Polynomial.X) := he
  have h := congrArg (fun t : Polynomial L => t.coeff j) he'
  rw [Polynomial.coeff_map, polynomial_coeff_comp_C_mul_X, ← map_pow] at h
  exact h

/-- Axis restrictions and relative primality descend the whole
univariate fraction-field polynomial to the original coefficient ring. -/
theorem polynomial_in_coprime_linear_invariant_coefficients_descend
    (a b : R₂) (hc : IsRelPrime a b) (q : A₂) (f : Polynomial L)
    (hv : MvPolynomial.map ι q = Polynomial.aeval (C (ι a) * X 0 + C (ι b) * X 1 : Aₗ) f) :
    ∃ g : Polynomial R₂, g.map ι = f := by
  classical
  let S : Aₗ := C (ι a) * X 0 + C (ι b) * X 1
  let sx : Fin 2 → Polynomial R₂ := ![Polynomial.X, 0]
  let sy : Fin 2 → Polynomial R₂ := ![0, Polynomial.X]
  have hx : aeval (fun i => (sx i).map ι) S = Polynomial.C (ι a) * Polynomial.X := by
    simp [sx, S, Polynomial.algebraMap_apply]
  have hy : aeval (fun i => (sy i).map ι) S = Polynomial.C (ι b) * Polynomial.X := by
    simp [sy, S, Polynomial.algebraMap_apply]
  have hunit (j : ℕ) : ∃ c : R₂, ι c = f.coeff j := by
    apply fraction_coefficient_descends_of_coprime_multiples (a ^ j) (b ^ j) hc.pow (f.coeff j)
    · exact ⟨(aeval sx q).coeff j, invariant_parameter_coeff_mul_is_base_on_axis S q f hv sx a hx j⟩
    · exact ⟨(aeval sy q).coeff j, invariant_parameter_coeff_mul_is_base_on_axis S q f hv sy b hy j⟩
  choose c hc' using hunit
  refine ⟨∑ j ∈ f.support, Polynomial.monomial j (c j), ?_⟩
  change (Polynomial.mapRingHom ι) (∑ j ∈ f.support, Polynomial.monomial j (c j)) = f
  rw [map_sum]
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_monomial, hc']
  exact f.sum_monomial_eq

end DimensionFourDependence.Shear
