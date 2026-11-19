import DimensionFourDependence.SegreRulingRootForms
import DimensionFourDependence.SegreAlgebraicBoundaryConstants
import DimensionFourDependence.FullDimensionCoefficientEmbedding
import DimensionFourDependence.SegreProjectiveRulingCoordinates
import DimensionFourDependence.SegreRealizedBoundaryHessian
import DimensionFourDependence.ExtendedCoefficientEuler

/-! # The actual finite Segre boundary point constructs its original binary factorization -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K E G : Type u} [Field K] [CharZero K] [Field E] [Algebra K E]
    [Field G] [Algebra E G]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- A realized original Segre fiber and its actual finite boundary point
construct the finite binary linear-root description of the nonzero radial
pairing. Its original coefficient field embeds algebraically into the
actual normalized coordinate field. Its extended partials, dimension,
Euler weights and zero acceleration are all constructed internally. -/
theorem segre_realized_finite_boundary_constructs_radial_product_root_forms
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y)
    (c q k : coefficientField (K := K) Y) (x : Fin 4 → G) (y : Fin 4 → E)
    (R : FiberCoefficientRealization (Equiv.refl (Fin 4)) Y hY
      (segreGraphFunction (coefficientCoordinate (K := K) Y)) c q k x y)
    {d : ℕ} (hd : 0 < d) (hc0 : c ≠ 0)
    (hc : coefficientEuler Y hY c = algebraMap K _ ((d : K)⁻¹) * c)
    (htr : Algebra.trdeg K E = 3) (j : Fin 3) (hj : j ≠ 0)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hboundary : p ∈ projectiveClosureSet (L := E) x)
    (hinfty : X none ∈ p.asHomogeneousIdeal)
    (hR0 : segreRulingLinearPolynomial (y j.castSucc / y 0) j.castSucc 0 ∈ p.asHomogeneousIdeal)
    (hR1 : segreRulingLinearPolynomial (y j.castSucc / y 0) 3 (if j = 1 then 2 else 1) ∈ p.asHomogeneousIdeal)
    (hfinite : SegreFiniteRulingBoundaryPoint K y j p) :
    ∃ a : Fin 4, X (some a) ∉ p.asHomogeneousIdeal ∧
      ∃ C : IntermediateField (segreProjectiveRulingParameterField K y j p a)
          (projectivePrimeRatioField p (some a)),
        Module.Finite (segreProjectiveRulingParameterField K y j p a) C ∧
        ∃ (m s : Fin 3 → C) (ρ : projectivePrimeRatioField p (some a)),
          m ≠ 0 ∧ s ≠ 0 ∧ ρ ≠ 0 ∧
          algebraMap E _ (y 0 * R.coefficientMap c) =
            ((fun i => (m i : projectivePrimeRatioField p (some a))) ⬝ᵥ
              (fun i : Fin 3 => algebraMap E _ (y i.castSucc))) * ρ ∧
          ρ ^ d = (fun i => (s i : projectivePrimeRatioField p (some a))) ⬝ᵥ
            (fun i : Fin 3 => algebraMap E _ (y i.castSucc)) ∧
          (fun i => (s i : projectivePrimeRatioField p (some a))) ⬝ᵥ
            (fun i : Fin 3 => projectivePrimeRatioCoordinate p (some a) (some i.castSucc)) = 0 ∧
          (algebraMap E (projectivePrimeRatioField p (some a)) (y 0 * R.coefficientMap c)) ^ d =
            ((fun i => (s i : projectivePrimeRatioField p (some a))) ⬝ᵥ
              (fun i : Fin 3 => algebraMap E _ (y i.castSucc))) *
            ((fun i => (m i : projectivePrimeRatioField p (some a))) ⬝ᵥ
              (fun i : Fin 3 => algebraMap E _ (y i.castSucc))) ^ d ∧
          ρ = algebraMap E _ (y 0 * R.coefficientMap c) /
            ((fun i => (m i : projectivePrimeRatioField p (some a))) ⬝ᵥ
              (fun i : Fin 3 => algebraMap E _ (y i.castSucc))) := by
  obtain ⟨a, ha, _hκE, hκtr, halg⟩ := finite_segre_ruling_boundary_normalized_field_absolute_trdeg
    y j htr p hinfty hfinite
  let κ := projectivePrimeRatioField p (some a)
  let L := coefficientField (K := K) Y
  let U : Fin 3 → L := coefficientCoordinate (K := K) Y
  let g : L →ₐ[K] E := { toRingHom := R.coefficientMap, commutes' := R.scalar_image }
  let f := (IsScalarTower.toAlgHom K E κ).comp g
  let : Algebra L κ := f.toRingHom.toAlgebra
  let : IsScalarTower K L κ := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  let : Algebra.IsAlgebraic L κ := coefficient_extension_isAlgebraic_of_absolute_dimension_le
    Y hY κ hκtr.le
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
  have halgP (i : Fin 3) : IsAlgebraic P.fieldRange (b i) := by
    rw [hJ]
    exact halg i.castSucc
  have hcκ : coordinateEuler Z δ (f c) = (d : κ)⁻¹ * f c := by
    change coordinateEuler (fun i => algebraMap L κ (U i)) (extendedCoefficientPartial Y hY κ)
      (algebraMap L κ c) = _
    rw [extendedCoefficientEuler_extends, hc]
    simp only [map_mul, map_inv₀, map_natCast]
    rfl
  have hHess : matrixBilinearPairing (derivationHessian δ (Z 0 * f c)) b b = 0 := by
    rw [show Z 0 * f c = algebraMap L κ (U 0 * c) from (map_mul f _ _).symm,
      extendedCoefficientPartial_hessian]
    exact segre_realized_projective_prime_radial_product_hessian_zero Y hY c q k x y R p hboundary hinfty a ha
  have hdata := segre_nonzero_radial_product_finite_linear_root_forms P δ Z b hcoord hcomm
    hZ0 j hPX hb hruling halgP hκtr.le hd (f c) ((map_ne_zero f).mpr hc0) hcκ hHess
  rw [hJ] at hdata
  obtain ⟨C, hC, m, s, ρ, hm, hs, hρ, hfactor, hroot, hsv, _hDρ, hpower, hformula⟩ := hdata
  have hF : Z 0 * f c = algebraMap E κ (y 0 * R.coefficientMap c) := by
    rw [hZ 0, map_mul]
    rfl
  rw [hF] at hfactor hpower hformula
  have hZF : Z = (fun i : Fin 3 => algebraMap E κ (y i.castSucc)) := funext hZ
  refine ⟨a, ha, C, hC, m, s, ρ, hm, hs, hρ, ?_, ?_, hsv, ?_, ?_⟩
  · simpa only [hZF] using hfactor
  · simpa only [hZF] using hroot
  · simpa only [hZF] using hpower
  · simpa only [hZF] using hformula

end DimensionFourDependence
