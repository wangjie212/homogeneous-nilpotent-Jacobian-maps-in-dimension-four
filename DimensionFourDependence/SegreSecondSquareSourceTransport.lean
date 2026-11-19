import DimensionFourDependence.SegreGlobalFactorizationTransport

/-! # The same original second-invariant hyperplane square in the source field -/

namespace DimensionFourDependence

open Matrix MvPolynomial
attribute [local instance] coefficientFieldScalarTower

universe u
set_option maxHeartbeats 3000000

variable {K F E : Type u} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]

/-- A faithful compatible realization reflects the same scalar and
constant covector in the radial-second-invariant square identity. -/
theorem radial_second_hyperplane_square_reflects_of_coordinate_images
    (φ : F →ₐ[K] E) (Y : Fin 4 → F) (Z : Fin 4 → E)
    (hcoord : ∀ i, φ (Y i) = Z i) (f : F) (g : E) (hf : φ f = g)
    (γ : K) (S : Fin 4 → K) (d : ℕ)
    (he : g ^ d = algebraMap K E γ * (((fun i => algebraMap K E (S i)) ⬝ᵥ Z) ^ 2)) :
    f ^ d = algebraMap K F γ * (((fun i => algebraMap K F (S i)) ⬝ᵥ Y) ^ 2) := by
  apply φ.injective
  change φ (f ^ d) = φ (algebraMap K F γ * (((fun i => algebraMap K F (S i)) ⬝ᵥ Y) ^ 2))
  simpa only [map_mul, map_pow, φ.commutes, constant_covector_pairing_algHom,
    funext hcoord, hf] using he

variable [CharZero K] {G : Type u} [Field G] [Algebra E G]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The specified original realized Segre fiber reflects its global
second-invariant square into the original source fraction field with
the very same original scalar and constant hyperplane covector. -/
theorem segre_realized_radial_second_square_reflects_to_original_source
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hind : ¬ComponentsDependent H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (hY : AlgebraicIndependent K (segreOriginalOutputTriple H))
    (q k : coefficientField (K := K) (segreOriginalOutputTriple H))
    (x : Fin 4 → G) (y : Fin 4 → E)
    (R : FiberCoefficientRealization (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY
      (segreOriginalCoefficientGraph H) 0 q k x y)
    (γ : K) (S : Fin 4 → K) (d : ℕ)
    (he : (y 0 * R.coefficientMap q) ^ d =
      algebraMap K E γ * (((fun i => algebraMap K E (S i)) ⬝ᵥ y) ^ 2)) :
    (algebraMap (MvPolynomial (Fin 4) K) S₀ (H 0) * (q : S₀)) ^ d =
      algebraMap K S₀ γ * (((fun i => algebraMap K S₀ (S i)) ⬝ᵥ
        (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) ^ 2) := by
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
  have hprod : g (U 0 * q) = y 0 * R.coefficientMap q := by
    rw [map_mul]
    exact congrArg (fun z => z * R.coefficientMap q) (R.coordinate_image 0)
  have hL := radial_second_hyperplane_square_reflects_of_coordinate_images
    g Z y hg (U 0 * q) _ hprod γ S d he
  let φ := IsScalarTower.toAlgHom K L S₀
  have hsource (i : Fin 4) : φ (Z i) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H i) := by
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact segre_original_coefficient_graph_value H hind hSegre
  have hsourceprod : φ (U 0 * q) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H 0) * (q : S₀) := rfl
  have hpair : φ ((fun i => algebraMap K L (S i)) ⬝ᵥ Z) =
      ((fun i => algebraMap K S₀ (S i)) ⬝ᵥ (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) := by
    rw [constant_covector_pairing_algHom, funext hsource]
  have hm := congrArg φ hL
  simpa only [map_mul, map_pow, φ.commutes, hsourceprod, hpair] using hm

end DimensionFourDependence
