import DimensionFourDependence.SegreCommonFieldBivariateDescent
import DimensionFourDependence.FullDimensionCoefficientEmbedding
import DimensionFourDependence.ExtendedCoefficientPartials

/-! # The actual original coefficient embedding constructs the bivariate Segre polynomial -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [CharZero K] [IsAlgClosed K] [Field E] [Algebra K E]
attribute [local instance] coefficientFieldScalarTower
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The specified embedding of the actual independent-output coefficient
field constructs all compatible original ratio derivatives and the
original bivariate polynomial. The dimension bound constructs the needed
algebraic extension; no extended partials or descent argument are supplied. -/
theorem segre_coefficient_embedding_constructs_bivariate_normalized_pairing
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y)
    (g : coefficientField (K := K) Y →ₐ[K] E) (Z : Fin 4 → E)
    (hg : ∀ i, g (coefficientCoordinate (K := K) Y i) = Z i.castSucc)
    (htr : Algebra.trdeg K E ≤ 3) (f : E) (d : ℕ)
    (hfirst : SegreAlgebraicNormalizedRulingPolynomial K Z f d 2)
    (hsecond : SegreAlgebraicNormalizedRulingPolynomial K Z f d 1) :
    SegreBivariateNormalizedPairingPolynomial K Z f d := by
  let L := coefficientField (K := K) Y
  let : Algebra L E := g.toRingHom.toAlgebra
  let : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq (fun r => (g.commutes r).symm)
  let : Algebra.IsAlgebraic L E := coefficient_extension_isAlgebraic_of_absolute_dimension_le Y hY E htr
  let δ := extendedCoefficientPartial Y hY E
  have hcoord (i j : Fin 3) : δ i (Z j.castSucc) = if j = i then 1 else 0 := by
    rw [← hg j]
    change extendedCoefficientPartial Y hY E i
      (algebraMap L E (coefficientCoordinate (K := K) Y j)) = _
    exact extendedCoefficientPartial_coordinate Y hY E i j
  have hcomm (i j : Fin 3) (a : E) : δ i (δ j a) = δ j (δ i a) :=
    extendedCoefficientPartials_commute Y hY E i j a
  have hU0 : coefficientCoordinate (K := K) Y 0 ≠ 0 := by
    intro hz
    apply (hY.transcendental 0).ne_zero
    simpa only [coefficientCoordinate_coe, IntermediateField.coe_zero] using
      congrArg (fun a : L => (a : S₀)) hz
  have hZ0 : Z 0 ≠ 0 := by
    have hcast : (0 : Fin 3).castSucc = (0 : Fin 4) := by decide
    simpa only [hg 0, hcast] using (map_ne_zero g).mpr hU0
  exact segre_two_common_ruling_polynomials_construct_bivariate_polynomial δ Z hcoord hcomm hZ0
    f d hfirst hsecond

end DimensionFourDependence
