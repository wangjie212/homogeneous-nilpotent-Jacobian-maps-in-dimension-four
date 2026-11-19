import DimensionFourDependence.BivariateAlgebraicPolynomialDescent
import DimensionFourDependence.SegreCommonFieldRulingPolynomials
import DimensionFourDependence.SegreRatioDerivations

/-! # The original scale-free Segre pairing is an original bivariate polynomial -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [Field E] [Algebra K E]

/-- A nonzero polynomial over the original constants, in the two
original Segre ratios, representing the original normalized radial
pairing and satisfying both independent degree bounds. -/
def SegreBivariateNormalizedPairingPolynomial
    (K : Type u) [Field K] [Algebra K E] (Y : Fin 4 → E) (f : E) (d : ℕ) : Prop :=
  ∃ B : Polynomial (Polynomial K), B ≠ 0 ∧ B.natDegree ≤ d + 1 ∧
    (∀ i, (B.coeff i).natDegree ≤ d + 1) ∧
    f ^ d / (Y 0) ^ (d + 1) =
      Polynomial.eval₂ (Polynomial.aeval (Y 2 / Y 0)).toRingHom (Y 1 / Y 0) B

/-- The actual original coordinate partials and the two common-field
ruling polynomials construct the original bivariate polynomial. No
derivative nilpotence, coefficient comparison, repeated integration
or bivariate descent is assumed. -/
theorem segre_two_common_ruling_polynomials_construct_bivariate_polynomial
    [CharZero K] [IsAlgClosed K]
    (δ : Fin 3 → Derivation K E E) (Y : Fin 4 → E)
    (hcoord : ∀ i j, δ i (Y j.castSucc) = if j = i then 1 else 0)
    (hcomm : ∀ i j x, δ i (δ j x) = δ j (δ i x)) (hY0 : Y 0 ≠ 0)
    (f : E) (d : ℕ)
    (hfirst : SegreAlgebraicNormalizedRulingPolynomial K Y f d 2)
    (hsecond : SegreAlgebraicNormalizedRulingPolynomial K Y f d 1) :
    SegreBivariateNormalizedPairingPolynomial K Y f d := by
  obtain ⟨P, hP, hPdegree, hPvalue, hPcoeff⟩ := hfirst
  obtain ⟨Q, _hQ, hQdegree, hQvalue, hQcoeff⟩ := hsecond
  let Z : Fin 3 → E := fun i => Y i.castSucc
  let s := Y 1 / Y 0
  let t := Y 2 / Y 0
  let Ds := segreRatioDerivation δ Z 1
  let Dt := segreRatioDerivation δ Z 2
  have hcast0 : (0 : Fin 3).castSucc = (0 : Fin 4) := by decide
  have hcast1 : (1 : Fin 3).castSucc = (1 : Fin 4) := by decide
  have hcast2 : (2 : Fin 3).castSucc = (2 : Fin 4) := by decide
  have hss : Ds s = 1 := by
    simpa only [Ds, s, Z, hcast0, hcast1, ite_true] using segreRatioDerivation_ratio δ Z hcoord hY0 1 (by decide) 1
  have hst : Ds t = 0 := by
    simpa only [Ds, t, Z, hcast0, hcast2, show (2 : Fin 3) ≠ 1 from by decide, ite_false] using
      segreRatioDerivation_ratio δ Z hcoord hY0 1 (by decide) 2
  have hts : Dt s = 0 := by
    simpa only [Dt, s, Z, hcast0, hcast1, show (1 : Fin 3) ≠ 2 from by decide, ite_false] using
      segreRatioDerivation_ratio δ Z hcoord hY0 2 (by decide) 1
  have htt : Dt t = 1 := by
    simpa only [Dt, t, Z, hcast0, hcast2, ite_true] using segreRatioDerivation_ratio δ Z hcoord hY0 2 (by decide) 2
  have hDsDt (x : E) : Ds (Dt x) = Dt (Ds x) :=
    segreRatioDerivations_commute δ Z hcoord hcomm 1 2 (by decide) (by decide) x
  change f ^ d / (Y 0) ^ (d + 1) = P.eval s at hPvalue
  change f ^ d / (Y 0) ^ (d + 1) = Q.eval t at hQvalue
  obtain ⟨B, hB, hdegree, hcoeffDegree, hvalue⟩ :=
    two_algebraic_parameter_polynomials_construct_bivariate_polynomial Ds Dt s t hss hst hts htt hDsDt
      P Q hP (d + 1) (d + 1) hPdegree hQdegree hPcoeff hQcoeff (hPvalue.symm.trans hQvalue)
  exact ⟨B, hB, hdegree, hcoeffDegree, hPvalue.trans hvalue⟩

end DimensionFourDependence
