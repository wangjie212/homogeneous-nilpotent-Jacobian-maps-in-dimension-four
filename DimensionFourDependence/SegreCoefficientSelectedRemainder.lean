import DimensionFourDependence.SegreSelectedGlobalRemainder
import DimensionFourDependence.FullDimensionCoefficientEmbedding
import DimensionFourDependence.ExtendedCoefficientPartials
import DimensionFourDependence.SegreRatioDerivations

/-! # Original coefficient coordinates derive selected-point incidence on the global remainder -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [CharZero K] [Field E] [IsAlgClosed E] [Algebra K E]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual original independent-output coefficient embedding
constructs the transverse ruling derivative and proves selected-point
incidence on a specified original global remainder hyperplane. -/
theorem segre_coefficient_embedding_selected_point_mem_global_remainder_hyperplane
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y)
    (g : coefficientField (K := K) Y →ₐ[K] E) (Z : Fin 4 → E)
    (hg : ∀ i, g (coefficientCoordinate (K := K) Y i) = Z i.castSucc)
    (htr : Algebra.trdeg K E ≤ 3) (hSegre : Z 0 * Z 3 - Z 1 * Z 2 = 0)
    (f : E) (hf : f ≠ 0) (d : ℕ) (hd : 1 < d)
    (j : Fin 3) (hj : j ≠ 0)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hR0 : segreRulingLinearPolynomial (Z j.castSucc / Z 0) j.castSucc 0 ∈ p.asHomogeneousIdeal)
    (hR1 : segreRulingLinearPolynomial (Z j.castSucc / Z 0) 3 (if j = 1 then 2 else 1) ∈ p.asHomogeneousIdeal)
    (hfactor : SegreFiniteRadialProductFactorization K Z f d j p)
    (a b : Fin 4 → K)
    (hglobal : f ^ d = ((fun i => algebraMap K E (a i)) ⬝ᵥ Z) *
      ((fun i => algebraMap K E (b i)) ⬝ᵥ Z) ^ d) :
    rename some (linearFormPolynomial (fun i => algebraMap K E (a i))) ∈ p.asHomogeneousIdeal := by
  let L := coefficientField (K := K) Y
  let : Algebra L E := g.toRingHom.toAlgebra
  let : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq (fun r => (g.commutes r).symm)
  let : Algebra.IsAlgebraic L E := coefficient_extension_isAlgebraic_of_absolute_dimension_le Y hY E htr
  let δ := extendedCoefficientPartial Y hY E
  have hcoord (i k : Fin 3) : δ i (Z k.castSucc) = if k = i then 1 else 0 := by
    rw [← hg k]
    change extendedCoefficientPartial Y hY E i
      (algebraMap L E (coefficientCoordinate (K := K) Y k)) = _
    exact extendedCoefficientPartial_coordinate Y hY E i k
  have hU0 : coefficientCoordinate (K := K) Y 0 ≠ 0 := by
    intro hz
    apply (hY.transcendental 0).ne_zero
    simpa only [coefficientCoordinate_coe, IntermediateField.coe_zero] using
      congrArg (fun a : L => (a : S₀)) hz
  have hcast0 : (0 : Fin 3).castSucc = (0 : Fin 4) := by decide
  have hZ0 : Z 0 ≠ 0 := by
    simpa only [hg 0, hcast0] using (map_ne_zero g).mpr hU0
  let W : Fin 3 → E := fun i => Z i.castSucc
  let k := segreRulingRemainingIndex j
  let D := segreRatioDerivation δ W k
  have hk : k ≠ 0 := by fin_cases j <;> decide
  have hjk : j ≠ k := by fin_cases j <;> decide
  have hfixed : D (Z j.castSucc / Z 0) = 0 := by
    simpa only [D, W, hcast0, hjk, ite_false] using
      segreRatioDerivation_ratio δ W hcoord hZ0 k hk j
  have hvarying : D (Z (segreRulingRemainingIndex j).castSucc / Z 0) = 1 := by
    simpa only [D, W, hcast0, ite_true] using
      segreRatioDerivation_ratio δ W hcoord hZ0 k hk k
  exact segre_selected_finite_ruling_point_mem_global_remainder_hyperplane
    Z hZ0 hSegre f hf d hd j hj D hfixed hvarying p hR0 hR1 hfactor a b hglobal

end DimensionFourDependence
