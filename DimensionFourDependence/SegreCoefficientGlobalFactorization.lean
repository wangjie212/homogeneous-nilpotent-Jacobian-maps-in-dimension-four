import DimensionFourDependence.SegreCommonFactorsGlobalIdentity
import DimensionFourDependence.FullDimensionCoefficientEmbedding
import DimensionFourDependence.ExtendedCoefficientPartials

/-! # The actual coefficient realization constructs the global radial power factors -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [CharZero K] [Field E] [IsAlgClosed E] [Algebra K E]
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The specified original independent-output coefficient embedding
and both actual finite boundary factorizations construct the global
constant hyperplanes. The actual coordinate partials, common-field
factors, rational restrictions and global divisor factors are derived. -/
theorem segre_coefficient_embedding_constructs_global_radial_hyperplanes
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y)
    (g : coefficientField (K := K) Y →ₐ[K] E) (Z : Fin 4 → E)
    (hg : ∀ i, g (coefficientCoordinate (K := K) Y i) = Z i.castSucc)
    (htr : Algebra.trdeg K E ≤ 3) (hSegre : Z 0 * Z 3 - Z 1 * Z 2 = 0)
    (f : E) (hf : f ≠ 0) (d : ℕ) (hd : 1 < d)
    (p r : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Option (Fin 4)) E))
    (hfirst : SegreFiniteRadialProductFactorization K Z f d 2 p)
    (hsecond : SegreFiniteRadialProductFactorization K Z f d 1 r)
    (hpoly : SegreBivariateNormalizedPairingPolynomial K Z f d) :
    ∃ a b : Fin 4 → K, a ≠ 0 ∧ b ≠ 0 ∧
      ((fun i => algebraMap K E (a i)) ⬝ᵥ Z) ≠ 0 ∧
      ((fun i => algebraMap K E (b i)) ⬝ᵥ Z) ≠ 0 ∧
      f ^ d = ((fun i => algebraMap K E (a i)) ⬝ᵥ Z) *
        ((fun i => algebraMap K E (b i)) ⬝ᵥ Z) ^ d := by
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
  have hU0 : coefficientCoordinate (K := K) Y 0 ≠ 0 := by
    intro hz
    apply (hY.transcendental 0).ne_zero
    simpa only [coefficientCoordinate_coe, IntermediateField.coe_zero] using
      congrArg (fun a : L => (a : S₀)) hz
  have hZ0 : Z 0 ≠ 0 := by
    have hcast : (0 : Fin 3).castSucc = (0 : Fin 4) := by decide
    simpa only [hg 0, hcast] using (map_ne_zero g).mpr hU0
  have hfirstCommon := finite_segre_ruling_factors_descend_to_common_geometric_constants
    Z f d 2 (by decide) hZ0 p hfirst
  have hsecondCommon := finite_segre_ruling_factors_descend_to_common_geometric_constants
    Z f d 1 (by decide) hZ0 r hsecond
  exact segre_common_ruling_factorizations_construct_global_radial_hyperplanes
    δ Z hcoord hZ0 hSegre f hf d hd hpoly hfirstCommon hsecondCommon

end DimensionFourDependence
