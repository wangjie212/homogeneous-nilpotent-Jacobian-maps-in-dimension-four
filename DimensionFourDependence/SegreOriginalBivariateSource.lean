import DimensionFourDependence.SegreBivariateEvaluationTransport
import DimensionFourDependence.SegreOriginalFiberWitness
import DimensionFourDependence.SegreFiberCoordinates

/-! # The original bivariate polynomial identity holds in the actual source field -/

namespace DimensionFourDependence

open MvPolynomial
attribute [local instance] coefficientFieldScalarTower

universe u
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K E G : Type u} [Field K] [CharZero K] [Field E] [Algebra K E]
    [Field G] [Algebra E G]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- Faithfulness of the actual geometric coefficient realization
reflects the bivariate identity to the original algebraic coefficient
field, then its actual inclusion gives the same polynomial identity in
the original source fraction field. The original three outputs and the
actual first invariant are retained. -/
theorem segre_realized_bivariate_pairing_identity_reflects_to_original_source
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    (hY : AlgebraicIndependent K (segreOriginalOutputTriple H))
    (c q k : coefficientField (K := K) (segreOriginalOutputTriple H))
    (x : Fin 4 → G) (y : Fin 4 → E)
    (R : FiberCoefficientRealization (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY
      (segreOriginalCoefficientGraph H) c q k x y)
    (d : ℕ)
    (hpoly : SegreBivariateNormalizedPairingPolynomial K y (y 0 * R.coefficientMap c) d) :
    SegreBivariateNormalizedPairingPolynomial K
      (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))
      (algebraMap (MvPolynomial (Fin 4) K) S₀ (H 0) * (c : S₀)) d := by
  let L := coefficientField (K := K) (segreOriginalOutputTriple H)
  let U : Fin 3 → L := coefficientCoordinate (K := K) (segreOriginalOutputTriple H)
  let Z : Fin 4 → L := segreGraphTarget U
  let g : L →ₐ[K] E := { toRingHom := R.coefficientMap, commutes' := R.scalar_image }
  have hZ (i : Fin 3) : Z i.castSucc = U i := by fin_cases i <;> rfl
  have hcoord (i : Fin 3) : g (Z i.castSucc) = y i.castSucc := by
    rw [hZ]
    exact R.coordinate_image i
  have hcast0 : (0 : Fin 3).castSucc = (0 : Fin 4) := by decide
  have hprod : g (U 0 * c) = y 0 * R.coefficientMap c := by
    rw [map_mul]
    change R.coefficientMap (U 0) * R.coefficientMap c = _
    have h0 : R.coefficientMap (U 0) = y 0 := by
      simpa only [Equiv.refl_apply, hcast0] using R.coordinate_image 0
    rw [h0]
  have hL : SegreBivariateNormalizedPairingPolynomial K Z (U 0 * c) d :=
    segre_bivariate_normalized_pairing_reflects_of_coordinate_images g Z y hcoord
      (U 0 * c) _ hprod d hpoly
  let φ := IsScalarTower.toAlgHom K L S₀
  apply segre_bivariate_normalized_pairing_map_of_coordinate_images φ Z
    (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) _ (U 0 * c) _ _ d hL
  · intro i
    fin_cases i <;> rfl
  · rfl

end DimensionFourDependence
