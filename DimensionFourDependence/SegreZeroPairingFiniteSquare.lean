import DimensionFourDependence.ParametricStationarySquareForms
import DimensionFourDependence.SegreRealizedZeroPairingBoundary
import DimensionFourDependence.SegreAlgebraicBoundaryConstants
import DimensionFourDependence.FullDimensionCoefficientEmbedding
import DimensionFourDependence.SegreProjectiveRulingCoordinates
import DimensionFourDependence.ExtendedCoefficientEuler
import DimensionFourDependence.SegreRulingDirectionCalculus

/-! # An actual zero-pairing finite boundary point constructs the original ruling-wise square factorization -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 100000

variable {K E G : Type u} [Field K] [CharZero K] [Field E] [Algebra K E]
    [Field G] [Algebra E G]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual radial second-invariant function has a dth power equal
to a nonzero finite-parameter scalar times the square of a linear form.
The selected original point is a zero of that same linear form. -/
def SegreFiniteRadialSecondSquareFactorization
    (K : Type u) [Field K] [Algebra K E] (y : Fin 4 → E) (f : E) (d : ℕ) (j : Fin 3)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E)) : Prop :=
  ∃ a : Fin 4, X (some a) ∉ p.asHomogeneousIdeal ∧
    ∃ C : IntermediateField (segreProjectiveRulingParameterField K y j p a)
        (projectivePrimeRatioField p (some a)),
      Module.Finite (segreProjectiveRulingParameterField K y j p a) C ∧
      ∃ (α : C) (S : Fin 3 → C), α ≠ 0 ∧ S ≠ 0 ∧
        (algebraMap E (projectivePrimeRatioField p (some a)) f) ^ d =
          (α : projectivePrimeRatioField p (some a)) *
            ((fun i => (S i : projectivePrimeRatioField p (some a))) ⬝ᵥ
              (fun i : Fin 3 => algebraMap E _ (y i.castSucc))) ^ 2 ∧
        ((fun i => (S i : projectivePrimeRatioField p (some a))) ⬝ᵥ
          (fun i : Fin 3 => projectivePrimeRatioCoordinate p (some a) (some i.castSucc))) = 0 ∧
        ((fun i => (S i : projectivePrimeRatioField p (some a))) ⬝ᵥ
          (fun i : Fin 3 => algebraMap E _ (y i.castSucc))) ≠ 0

/-- The actual original zero-pairing realization and selected finite
ruling point construct the scalar-times-linear-square identity of
Section 5.4. Its parameter field, finite coefficients, actual direction,
stationarity, Euler weights and dimension are all derived internally. -/
theorem segre_realized_zero_pairing_finite_boundary_constructs_radial_second_square_factorization
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y)
    (q k : coefficientField (K := K) Y) (x : Fin 4 → G) (y : Fin 4 → E)
    (R : FiberCoefficientRealization (Equiv.refl (Fin 4)) Y hY
      (segreGraphFunction (coefficientCoordinate (K := K) Y)) 0 q k x y)
    (d : ℕ) (hd : 0 < d) (hq0 : q ≠ 0)
    (hq : coefficientEuler Y hY q = algebraMap K _ (2 * (d : K)⁻¹ - 1) * q)
    (htr : Algebra.trdeg K E = 3) (j : Fin 3) (hj : j ≠ 0)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hboundary : p ∈ projectiveClosureSet (L := E) x) (hinfty : X none ∈ p.asHomogeneousIdeal)
    (hR0 : segreRulingLinearPolynomial (y j.castSucc / y 0) j.castSucc 0 ∈ p.asHomogeneousIdeal)
    (hR1 : segreRulingLinearPolynomial (y j.castSucc / y 0) 3 (if j = 1 then 2 else 1) ∈ p.asHomogeneousIdeal)
    (hfinite : SegreFiniteRulingBoundaryPoint K y j p) :
    SegreFiniteRadialSecondSquareFactorization K y (y 0 * R.coefficientMap q) d j p := by
  obtain ⟨a, ha, _hκE, hκtr, halg⟩ := finite_segre_ruling_boundary_normalized_field_absolute_trdeg
    y j htr p hinfty hfinite
  let κ := projectivePrimeRatioField p (some a)
  let L := coefficientField (K := K) Y
  let U : Fin 3 → L := coefficientCoordinate (K := K) Y
  let g : L →ₐ[K] E := { toRingHom := R.coefficientMap, commutes' := R.scalar_image }
  let f := (IsScalarTower.toAlgHom K E κ).comp g
  let : Algebra L κ := f.toRingHom.toAlgebra
  let : IsScalarTower K L κ := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  let : Algebra.IsAlgebraic L κ := coefficient_extension_isAlgebraic_of_absolute_dimension_le Y hY κ hκtr.le
  let δ := extendedCoefficientPartial Y hY κ
  let Z : Fin 3 → κ := fun i => f (U i)
  let b : Fin 3 → κ := fun i => projectivePrimeRatioCoordinate p (some a) (some i.castSucc)
  let P : RatFunc K →ₐ[K] κ := f.comp (segreCoefficientRulingParameterHom Y hY j hj)
  have hZ (i : Fin 3) : Z i = algebraMap E κ (y i.castSucc) := by
    change algebraMap E κ (R.coefficientMap (U i)) = _
    rw [R.coordinate_image]
    rfl
  have hU0 : U 0 ≠ 0 := by
    intro he
    apply (hY.transcendental 0).ne_zero
    simpa only [U, coefficientCoordinate_coe, IntermediateField.coe_zero] using
      congrArg (fun a : L => (a : S₀)) he
  have hZ0 : Z 0 ≠ 0 := (map_ne_zero f).mpr hU0
  have hcoord : ∀ i j, δ i (Z j) = if j = i then 1 else 0 :=
    extendedCoefficientPartial_coordinate Y hY κ
  have hcomm : ∀ i j r, δ i (δ j r) = δ j (δ i r) := extendedCoefficientPartials_commute Y hY κ
  have hPX : P RatFunc.X = Z j / Z 0 := by
    change f (segreCoefficientRulingParameterHom Y hY j hj RatFunc.X) = f (U j) / f (U 0)
    rw [segreCoefficientRulingParameterHom_X]
    exact map_div₀ f _ _
  have hJ : P.fieldRange = segreProjectiveRulingParameterField K y j p a := by
    rw [rational_function_algHom_fieldRange_eq_adjoin_parameter, hPX, hZ j, hZ 0, ← map_div₀]
    rfl
  have hba : (fun i : Fin 4 => projectivePrimeRatioCoordinate p (some a) (some i)) ≠ 0 := by
    intro he
    have hz := congrFun he a
    rw [projectivePrimeRatioCoordinate_self p (some a) ha] at hz
    exact one_ne_zero hz
  have hkernel := segre_normalized_projective_ruling_kernel y j hj p a ha hR0 hR1
  have hb : b ≠ 0 := segre_ruling_kernel_first_three_ne_zero j hj _ _ hba hkernel
  have hruling : b j = (Z j / Z 0) * b 0 := by
    rw [hZ j, hZ 0, ← map_div₀]
    exact segreRulingMatrix_kernel_coordinate_relation j hj _ _ hkernel
  have halgP (i : Fin 3) : IsAlgebraic P.fieldRange (b i) := by rw [hJ]; exact halg i.castSucc
  have htD : coordinateEuler b δ (P RatFunc.X) = 0 := by
    rw [hPX]
    exact segre_ruling_direction_fixes_coordinate_ratio δ Z b hcoord hZ0 j hruling
  have htE : coordinateEuler Z δ (P RatFunc.X) = 0 := by
    rw [hPX]
    exact segre_output_euler_fixes_coordinate_ratio δ Z hcoord j
  have hqκ : coordinateEuler Z δ (f q) = (2 * (d : κ)⁻¹ - 1) * f q := by
    change coordinateEuler (fun i => algebraMap L κ (U i)) (extendedCoefficientPartial Y hY κ)
      (algebraMap L κ q) = _
    rw [extendedCoefficientEuler_extends, hq]
    simp only [map_mul, map_sub, map_inv₀, map_natCast, map_ofNat, map_one]
    rfl
  have hweight : coordinateEuler Z δ (Z 0 * f q) = (2 * (d : κ)⁻¹) * (Z 0 * f q) := by
    have he := segre_radial_product_euler_weight δ Z hcoord (f q) _ hqκ
    convert he using 1 <;> ring
  have hDf : coordinateEuler b δ (Z 0 * f q) = 0 := by
    rw [show Z 0 * f q = algebraMap L κ (U 0 * q) from (map_mul f _ _).symm]
    change (∑ i : Fin 3, b i * extendedCoefficientPartial Y hY κ i
      (algebraMap L κ (U 0 * q))) = 0
    have hext (i : Fin 3) : extendedCoefficientPartial Y hY κ i
        (algebraMap L κ (U 0 * q)) =
        algebraMap L κ (coefficientPartial Y hY i (U 0 * q)) :=
      extendedCoefficientPartial_extends Y hY κ i (U 0 * q)
    simp_rw [hext]
    change (∑ i : Fin 3, b i * algebraMap E κ
      (R.coefficientMap (coefficientPartial Y hY i (U 0 * q)))) = 0
    simpa only [b, mul_comm] using
      segre_realized_zero_pairing_projective_prime_radial_second_gradient_zero
        Y hY q k x y R p hboundary hinfty a ha
  have hdata := parametric_stationary_weight_two_finite_linear_square_form P δ Z b hcoord hcomm hb halgP
    htD htE hκtr.le d hd (Z 0 * f q) (mul_ne_zero hZ0 ((map_ne_zero f).mpr hq0)) hDf hweight
  rw [hJ] at hdata
  obtain ⟨C, hC, α, S, hα, hS, hpower, hSb, hSY⟩ := hdata
  have hF : Z 0 * f q = algebraMap E κ (y 0 * R.coefficientMap q) := by rw [hZ 0, map_mul]; rfl
  rw [hF] at hpower
  have hZF : Z = (fun i : Fin 3 => algebraMap E κ (y i.castSucc)) := funext hZ
  refine ⟨a, ha, C, hC, α, S, hα, hS, ?_, hSb, ?_⟩
  · simpa only [hZF] using hpower
  · simpa only [hZF] using hSY

end DimensionFourDependence
