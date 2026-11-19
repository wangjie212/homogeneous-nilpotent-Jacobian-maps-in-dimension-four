import DimensionFourDependence.SegreNormalizedSecondSquare
import DimensionFourDependence.SegreCommonFieldBivariateDescent

/-! # The original zero-pairing function has bidegree at most (2,2) -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    [Field E] [Algebra K E]

/-- Two original ruling polynomials with the specified separate degree
bounds construct a polynomial over the original algebraically closed
constants. The actual ratio derivations supply the descent hypotheses. -/
theorem segre_two_algebraic_ruling_polynomials_construct_original_bivariate_polynomial
    (δ : Fin 3 → Derivation K E E) (Y : Fin 4 → E)
    (hcoord : ∀ i j, δ i (Y j.castSucc) = if j = i then 1 else 0)
    (hcomm : ∀ i j x, δ i (δ j x) = δ j (δ i x)) (hY0 : Y 0 ≠ 0)
    (v : E) (P Q : Polynomial E) (hP : P ≠ 0) (N M : ℕ)
    (hPdegree : P.natDegree ≤ N) (hQdegree : Q.natDegree ≤ M)
    (hPvalue : v = P.eval (Y 1 / Y 0)) (hQvalue : v = Q.eval (Y 2 / Y 0))
    (hPcoeff : ∀ i, IsAlgebraic (IntermediateField.adjoin K ({Y 2 / Y 0} : Set E)) (P.coeff i))
    (hQcoeff : ∀ i, IsAlgebraic (IntermediateField.adjoin K ({Y 1 / Y 0} : Set E)) (Q.coeff i)) :
    ∃ B : Polynomial (Polynomial K), B ≠ 0 ∧ B.natDegree ≤ N ∧
      (∀ i, (B.coeff i).natDegree ≤ M) ∧
      v = Polynomial.eval₂ (Polynomial.aeval (Y 2 / Y 0)).toRingHom (Y 1 / Y 0) B := by
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
  have hDsDt (x : E) : Ds (Dt x) = Dt (Ds x) :=
    segreRatioDerivations_commute δ Z hcoord hcomm 1 2 (by decide) (by decide) x
  obtain ⟨B, hB, hdegree, hcoeffDegree, hvalue⟩ :=
    two_algebraic_parameter_polynomials_construct_bivariate_polynomial Ds Dt s t hss hst hts htt hDsDt
      P Q hP N M hPdegree hQdegree hPcoeff hQcoeff (hPvalue.symm.trans hQvalue)
  exact ⟨B, hB, hdegree, hcoeffDegree, hPvalue.trans hvalue⟩

/-- The same original normalized radial second invariant is an original
polynomial of bidegree at most (2,2). The two finite ruling descriptions
are not presumed to have compatible coefficient extensions. -/
theorem segre_two_second_square_ruling_polynomials_construct_original_biquadratic_polynomial
    (δ : Fin 3 → Derivation K E E) (Y : Fin 4 → E)
    (hcoord : ∀ i j, δ i (Y j.castSucc) = if j = i then 1 else 0)
    (hcomm : ∀ i j x, δ i (δ j x) = δ j (δ i x)) (hY0 : Y 0 ≠ 0)
    (f : E) (d : ℕ)
    (hfirst : SegreAlgebraicNormalizedSecondSquarePolynomial K Y f d 2)
    (hsecond : SegreAlgebraicNormalizedSecondSquarePolynomial K Y f d 1) :
    ∃ B : Polynomial (Polynomial K), B ≠ 0 ∧ B.natDegree ≤ 2 ∧
      (∀ i, (B.coeff i).natDegree ≤ 2) ∧
      f ^ d / Y 0 ^ 2 = Polynomial.eval₂ (Polynomial.aeval (Y 2 / Y 0)).toRingHom (Y 1 / Y 0) B := by
  obtain ⟨P, hP, hPdegree, hPvalue, hPcoeff⟩ := hfirst
  obtain ⟨Q, _hQ, hQdegree, hQvalue, hQcoeff⟩ := hsecond
  exact segre_two_algebraic_ruling_polynomials_construct_original_bivariate_polynomial
    δ Y hcoord hcomm hY0 (f ^ d / Y 0 ^ 2) P Q hP 2 2 hPdegree hQdegree
    hPvalue hQvalue hPcoeff hQcoeff

end DimensionFourDependence
