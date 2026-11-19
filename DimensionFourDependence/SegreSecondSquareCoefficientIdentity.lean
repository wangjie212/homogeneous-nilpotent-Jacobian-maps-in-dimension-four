import DimensionFourDependence.SegreSecondSquareGlobalIdentity
import DimensionFourDependence.SegreSecondSquareBivariateDescent
import DimensionFourDependence.FullDimensionCoefficientEmbedding
import DimensionFourDependence.ExtendedCoefficientPartials

/-! # The original coefficient embedding constructs the zero-pairing global square -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    [Field E] [IsAlgClosed E] [Algebra K E]
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The specified independent-output embedding and both actual finite
ruling squares construct one original constant scalar and hyperplane.
The actual extended partials, common-field coefficients, bivariate
polynomial, two rational restrictions and global square are all derived. -/
theorem segre_coefficient_embedding_constructs_global_radial_second_hyperplane_square
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y)
    (g : coefficientField (K := K) Y →ₐ[K] E) (Z : Fin 4 → E)
    (hg : ∀ i, g (coefficientCoordinate (K := K) Y i) = Z i.castSucc)
    (htr : Algebra.trdeg K E ≤ 3) (hSegre : Z 0 * Z 3 - Z 1 * Z 2 = 0)
    (f : E) (hf : f ≠ 0) (d : ℕ)
    (p r : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Option (Fin 4)) E))
    (hfirst : SegreFiniteRadialSecondSquareFactorization K Z f d 2 p)
    (hsecond : SegreFiniteRadialSecondSquareFactorization K Z f d 1 r) :
    ∃ (γ : K) (S : Fin 4 → K), γ ≠ 0 ∧ S ≠ 0 ∧
      ((fun i => algebraMap K E (S i)) ⬝ᵥ Z) ≠ 0 ∧
      f ^ d = algebraMap K E γ * (((fun i => algebraMap K E (S i)) ⬝ᵥ Z) ^ 2) := by
  let L := coefficientField (K := K) Y
  let : Algebra L E := g.toRingHom.toAlgebra
  let : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq (fun a => (g.commutes a).symm)
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
  have hfirstPoly := finite_segre_second_square_descends_to_geometric_constants
    Z f d 2 (by decide) hZ0 p hfirst
  have hsecondPoly := finite_segre_second_square_descends_to_geometric_constants
    Z f d 1 (by decide) hZ0 r hsecond
  obtain ⟨P, _hP, _hPdegree, _hPcoeffDegree, hPvalue⟩ :=
    segre_two_second_square_ruling_polynomials_construct_original_biquadratic_polynomial
      δ Z hcoord hcomm hZ0 f d hfirstPoly hsecondPoly
  have hfirstCommon := finite_segre_second_square_factors_descend_to_common_geometric_constants
    Z f d 2 (by decide) hZ0 p hfirst
  have hsecondCommon := finite_segre_second_square_factors_descend_to_common_geometric_constants
    Z f d 1 (by decide) hZ0 r hsecond
  exact segre_common_second_square_factorizations_construct_global_radial_hyperplane
    δ Z hcoord hZ0 hSegre f hf d P hPvalue hfirstCommon hsecondCommon

end DimensionFourDependence
