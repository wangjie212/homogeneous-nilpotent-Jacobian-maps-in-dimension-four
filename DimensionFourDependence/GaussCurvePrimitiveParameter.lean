import DimensionFourDependence.RationalGaussCurve
import DimensionFourDependence.PrimitiveRationalVector

/-! # A primitive polynomial covector for the actual rational Gauss parameter

Pull the actual normal-ratio coordinates back through the constructed
rational-function-field equivalence, clear their denominators, and remove
their gcd. Mapping the resulting polynomial covector into the original
source field gives the actual normal itself up to a nonzero scalar. The
parameter presentation needed for Section 4.1 is thus constructed.
-/

namespace DimensionFourDependence

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- The actual one-dimensional Gauss image has a constructed primitive
polynomial covector presentation in a rational source-field parameter,
with a nonzero actual scalar factor and all original normal coordinates. -/
theorem actual_gauss_curve_primitive_polynomial_parameter
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1) :
    ∃ v : Fin 4 → Polynomial K, v ≠ 0 ∧
      (∀ r : Polynomial K, (∀ i, r ∣ v i) → IsUnit r) ∧
      ∃ t c : FractionRing (MvPolynomial (Fin 4) K), c ≠ 0 ∧
        ∀ i, rationalImageNormal H I.equation i = c * Polynomial.aeval t (v i) := by
  let ν := rationalImageNormal H I.equation
  let a := imageNormalPivot H I
  let M := projectiveRatioField (K := K) ν a
  let x : Fin 4 → M := fullOutputCoordinate (K := K) (fun i => ν i / ν a)
  have ha : ν a ≠ 0 := imageNormalPivot_ne_zero H I
  have hxa : x a = 1 := by
    apply Subtype.ext
    change ν a / ν a = 1
    exact div_self ha
  obtain ⟨e⟩ := actual_gauss_curve_rational_function_field H I hGauss
  let b : Fin 4 → RatFunc K := fun i => e.symm (x i)
  have hb : b ≠ 0 := by
    intro hz
    have he := congrFun hz a
    have hba : b a = 1 := by
      change e.symm (x a) = 1
      rw [hxa, map_one]
    rw [hba, Pi.zero_apply] at he
    exact one_ne_zero he
  obtain ⟨v, hv, hprimitive, r, hr, hrep⟩ := rational_vector_primitive_polynomial_presentation b hb
  let f : RatFunc K →ₐ[K] FractionRing (MvPolynomial (Fin 4) K) := M.val.comp e.toAlgHom
  have hfr : f r ≠ 0 := by
    intro hz
    apply hr
    have he : f r = f 0 := by rw [hz, map_zero]
    exact f.injective he
  have hfcoord (i : Fin 4) : f (b i) = ν i / ν a := by
    change M.val (e (e.symm (x i))) = ν i / ν a
    rw [e.apply_symm_apply]
    rfl
  refine ⟨v, hv, hprimitive, f RatFunc.X, ν a * f r, mul_ne_zero ha hfr, ?_⟩
  intro i
  have he := congrArg f (hrep i)
  rw [hfcoord, map_mul, rational_function_algHom_polynomial_value] at he
  have hi := (div_eq_iff ha).mp he
  change ν i = (ν a * f r) * Polynomial.aeval (f RatFunc.X) (v i)
  calc
    _ = (f r * Polynomial.aeval (f RatFunc.X) (v i)) * ν a := hi
    _ = _ := by ring

end DimensionFourDependence
