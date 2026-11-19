import DimensionFourDependence.SegreOriginalBivariateSource
import DimensionFourDependence.SegreRulingGlobalPowerReduction

/-! # The same original constant radial hyperplanes in the geometric and source fields -/

namespace DimensionFourDependence

open Matrix MvPolynomial
attribute [local instance] coefficientFieldScalarTower

universe u
set_option maxHeartbeats 3000000

variable {K F E : Type u} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]

/-- The complete original constant covector evaluation is preserved
under a specified compatible geometric coefficient embedding. -/
theorem constant_covector_pairing_algHom {n : ℕ}
    (φ : F →ₐ[K] E) (a : Fin n → K) (Y : Fin n → F) :
    φ ((fun i => algebraMap K F (a i)) ⬝ᵥ Y) =
      ((fun i => algebraMap K E (a i)) ⬝ᵥ (fun i => φ (Y i))) := by
  simp only [dotProduct, map_sum, map_mul, φ.commutes]

/-- Faithfulness reflects the original radial-product equation with
the same two original constant covectors, not newly chosen factors. -/
theorem radial_hyperplane_power_identity_reflects_of_coordinate_images
    (φ : F →ₐ[K] E) (Y : Fin 4 → F) (Z : Fin 4 → E)
    (hcoord : ∀ i, φ (Y i) = Z i) (f : F) (g : E) (hf : φ f = g)
    (a b : Fin 4 → K) (d : ℕ)
    (he : g ^ d = ((fun i => algebraMap K E (a i)) ⬝ᵥ Z) *
      ((fun i => algebraMap K E (b i)) ⬝ᵥ Z) ^ d) :
    f ^ d = ((fun i => algebraMap K F (a i)) ⬝ᵥ Y) *
      ((fun i => algebraMap K F (b i)) ⬝ᵥ Y) ^ d := by
  apply φ.injective
  change φ (f ^ d) = φ (((fun i => algebraMap K F (a i)) ⬝ᵥ Y) *
    ((fun i => algebraMap K F (b i)) ⬝ᵥ Y) ^ d)
  simpa only [map_mul, map_pow, constant_covector_pairing_algHom, funext hcoord, hf] using he

variable [CharZero K] {G : Type u} [Field G] [Algebra E G]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual original Segre coefficient realization reflects the
global radial identity to its original source fraction field, retaining
both original hyperplane covectors and the actual first invariant. -/
theorem segre_realized_radial_hyperplane_power_identity_reflects_to_original_source
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hind : ¬ComponentsDependent H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (hY : AlgebraicIndependent K (segreOriginalOutputTriple H))
    (c q k : coefficientField (K := K) (segreOriginalOutputTriple H))
    (x : Fin 4 → G) (y : Fin 4 → E)
    (R : FiberCoefficientRealization (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY
      (segreOriginalCoefficientGraph H) c q k x y)
    (a b : Fin 4 → K) (d : ℕ)
    (he : (y 0 * R.coefficientMap c) ^ d =
      ((fun i => algebraMap K E (a i)) ⬝ᵥ y) * ((fun i => algebraMap K E (b i)) ⬝ᵥ y) ^ d) :
    (algebraMap (MvPolynomial (Fin 4) K) S₀ (H 0) * (c : S₀)) ^ d =
      ((fun i => algebraMap K S₀ (a i)) ⬝ᵥ
        (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) *
      ((fun i => algebraMap K S₀ (b i)) ⬝ᵥ
        (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) ^ d := by
  let L := coefficientField (K := K) (segreOriginalOutputTriple H)
  let U : Fin 3 → L := coefficientCoordinate (K := K) (segreOriginalOutputTriple H)
  let Z : Fin 4 → L := ![U 0, U 1, U 2, segreOriginalCoefficientGraph H]
  let g : L →ₐ[K] E := { toRingHom := R.coefficientMap, commutes' := R.scalar_image }
  have hg (i : Fin 4) : g (Z i) = y i := by
    fin_cases i
    · exact R.coordinate_image 0
    · exact R.coordinate_image 1
    · exact R.coordinate_image 2
    · exact R.last_output_image
  have hprod : g (U 0 * c) = y 0 * R.coefficientMap c := by
    rw [map_mul]
    exact congrArg (fun z => z * R.coefficientMap c) (R.coordinate_image 0)
  have hL := radial_hyperplane_power_identity_reflects_of_coordinate_images
    g Z y hg (U 0 * c) _ hprod a b d he
  let φ := IsScalarTower.toAlgHom K L S₀
  have hsource (i : Fin 4) : φ (Z i) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H i) := by
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact segre_original_coefficient_graph_value H hind hSegre
  have hsourceprod : φ (U 0 * c) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H 0) * (c : S₀) := rfl
  have hpair (a : Fin 4 → K) : φ ((fun i => algebraMap K L (a i)) ⬝ᵥ Z) =
      ((fun i => algebraMap K S₀ (a i)) ⬝ᵥ (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) := by
    rw [constant_covector_pairing_algHom, funext hsource]
  have hm := congrArg φ hL
  simpa only [map_mul, map_pow, hsourceprod, hpair] using hm

end DimensionFourDependence
