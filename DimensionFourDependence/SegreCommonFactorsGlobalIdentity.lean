import DimensionFourDependence.TwoRationalRulingPresentations
import DimensionFourDependence.SegreCommonFieldRulingFactors
import DimensionFourDependence.SegreRulingGlobalPowerReduction

/-! # The actual two common-field ruling factors construct the global radial identity -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [CharZero K] [Field E] [Algebra K E]

/-- The actual coordinate partials and both common-field factorizations
construct exact rational restrictions of the same original bivariate
polynomial, descend their factors, and produce two nonzero original
constant hyperplanes satisfying the global radial identity. -/
theorem segre_common_ruling_factorizations_construct_global_radial_hyperplanes
    (δ : Fin 3 → Derivation K E E) (Y : Fin 4 → E)
    (hcoord : ∀ i j, δ i (Y j.castSucc) = if j = i then 1 else 0)
    (hY0 : Y 0 ≠ 0) (hSegre : Y 0 * Y 3 - Y 1 * Y 2 = 0)
    (f : E) (hf : f ≠ 0) (d : ℕ) (hd : 1 < d)
    (hpoly : SegreBivariateNormalizedPairingPolynomial K Y f d)
    (hfirst : SegreAlgebraicNormalizedRulingFactorization K Y f d 2)
    (hsecond : SegreAlgebraicNormalizedRulingFactorization K Y f d 1) :
    ∃ r b : Fin 4 → K, r ≠ 0 ∧ b ≠ 0 ∧
      ((fun i => algebraMap K E (r i)) ⬝ᵥ Y) ≠ 0 ∧
      ((fun i => algebraMap K E (b i)) ⬝ᵥ Y) ≠ 0 ∧
      f ^ d = ((fun i => algebraMap K E (r i)) ⬝ᵥ Y) *
        ((fun i => algebraMap K E (b i)) ⬝ᵥ Y) ^ d := by
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  obtain ⟨P, _hP0, _hPdeg, _hPcoeffdeg, hPvalue⟩ := hpoly
  obtain ⟨a₁, b₁, ha₁, hb₁, hvalue₁⟩ := hfirst
  obtain ⟨a₂, b₂, ha₂, hb₂, hvalue₂⟩ := hsecond
  let Z : Fin 3 → E := fun i => Y i.castSucc
  let s := Y 1 / Y 0
  let t := Y 2 / Y 0
  let Ds := segreRatioDerivation δ Z 1
  let Dt := segreRatioDerivation δ Z 2
  have hcast0 : (0 : Fin 3).castSucc = (0 : Fin 4) := by decide
  have hcast1 : (1 : Fin 3).castSucc = (1 : Fin 4) := by decide
  have hcast2 : (2 : Fin 3).castSucc = (2 : Fin 4) := by decide
  have hss : Ds s = 1 := by
    simpa only [Ds, s, Z, hcast0, hcast1, ite_true] using
      segreRatioDerivation_ratio δ Z hcoord hY0 1 (by decide) 1
  have hst : Ds t = 0 := by
    simpa only [Ds, t, Z, hcast0, hcast2, show (2 : Fin 3) ≠ 1 from by decide, ite_false] using
      segreRatioDerivation_ratio δ Z hcoord hY0 1 (by decide) 2
  have hts : Dt s = 0 := by
    simpa only [Dt, s, Z, hcast0, hcast1, show (1 : Fin 3) ≠ 2 from by decide, ite_false] using
      segreRatioDerivation_ratio δ Z hcoord hY0 2 (by decide) 1
  have htt : Dt t = 1 := by
    simpa only [Dt, t, Z, hcast0, hcast2, ite_true] using
      segreRatioDerivation_ratio δ Z hcoord hY0 2 (by decide) 2
  have hrem1 : segreRulingRemainingIndex 1 = 2 := rfl
  have hrem2 : segreRulingRemainingIndex 2 = 1 := rfl
  have ha₁' : ∀ i, IsAlgebraic (IntermediateField.adjoin K ({t} : Set E)) (a₁ i) := by
    change ∀ i, IsAlgebraic (IntermediateField.adjoin K ({t} : Set E)) (a₁ i) at ha₁
    exact ha₁
  have hb₁' : ∀ i, IsAlgebraic (IntermediateField.adjoin K ({t} : Set E)) (b₁ i) := by
    change ∀ i, IsAlgebraic (IntermediateField.adjoin K ({t} : Set E)) (b₁ i) at hb₁
    exact hb₁
  have ha₂' : ∀ i, IsAlgebraic (IntermediateField.adjoin K ({s} : Set E)) (a₂ i) := by
    change ∀ i, IsAlgebraic (IntermediateField.adjoin K ({s} : Set E)) (a₂ i) at ha₂
    exact ha₂
  have hb₂' : ∀ i, IsAlgebraic (IntermediateField.adjoin K ({s} : Set E)) (b₂ i) := by
    change ∀ i, IsAlgebraic (IntermediateField.adjoin K ({s} : Set E)) (b₂ i) at hb₂
    exact hb₂
  have hv₁ : f ^ d / Y 0 ^ (d + 1) = (segreRulingPowerPolynomial a₁ b₁ d).eval s := by
    simpa only [s, hrem2, hcast1] using hvalue₁
  have hv₂ : f ^ d / Y 0 ^ (d + 1) = (segreRulingPowerPolynomial a₂ b₂ d).eval t := by
    simpa only [t, hrem1, hcast2] using hvalue₂
  obtain ⟨φ₁, φ₂, _hφ₁, _hφ₂, hfirstP, hsecondP⟩ :=
    two_parameter_algebraic_factored_values_construct_exact_rational_presentations
      Ds Dt s t hss hst hts htt P (f ^ d / Y 0 ^ (d + 1)) d a₁ b₁ a₂ b₂
      ha₁' hb₁' ha₂' hb₂' hPvalue hv₁ hv₂
  exact segre_two_extension_ruling_identities_construct_original_radial_hyperplanes
    P Y hY0 hSegre f hf d hd hPvalue φ₁.toRingHom φ₂.toRingHom a₁ b₁ a₂ b₂ hfirstP hsecondP

end DimensionFourDependence
