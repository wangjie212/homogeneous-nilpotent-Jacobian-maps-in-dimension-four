import DimensionFourDependence.RulingCoordinateBasis

/-! # Coordinate reconstruction for the specified dual ruling vectors

The coordinate-span construction is unique once its four dual values
are fixed. Consequently the particular vectors used to construct the
simple boundary chart give the coordinate formula on the entire
scalar-extended ruling.
-/

namespace DimensionFourDependence

open Matrix Module

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {n m : ℕ}

/-- Any specified pair with the four dual values agrees with the
coordinate-span construction and reconstructs every ruling vector. -/
theorem ruling_coordinates_of_specified_dual_pair
    (W : Submodule F (Fin n → F)) (hdim : finrank F W = 2)
    (s t b z : Fin n → F)
    (hpair : LinearIndependent F ![rulingFormRestriction W s, rulingFormRestriction W t])
    (hb : b ∈ W) (hz : z ∈ W)
    (hsb : s ⬝ᵥ b = 1) (htb : t ⬝ᵥ b = 0)
    (hsz : s ⬝ᵥ z = 0) (htz : t ⬝ᵥ z = 1) :
    ∀ x ∈ W, ∀ i, x i = b i * (s ⬝ᵥ x) + z i * (t ⬝ᵥ x) := by
  obtain ⟨b₀, z₀, hspan⟩ := two_dimensional_ruling_coordinate_form_span W hdim s t hpair
  have hb₀ : b₀ = b := by
    funext i
    simpa only [hsb, htb, mul_one, mul_zero, add_zero] using (hspan b hb i).symm
  have hz₀ : z₀ = z := by
    funext i
    simpa only [hsz, htz, mul_one, mul_zero, zero_add] using (hspan z hz i).symm
  rwa [hb₀, hz₀] at hspan

/-- The same specified dual pair reconstructs every point of the
actual extended matrix kernel, rather than an independently chosen basis. -/
theorem matrix_kernel_coordinates_of_specified_dual_pair_after_extension
    (A : Matrix (Fin m) (Fin n) F)
    (hdim : finrank F (LinearMap.ker A.toLin') = 2)
    (s t b z : Fin n → F)
    (hpair : LinearIndependent F ![rulingFormRestriction (LinearMap.ker A.toLin') s,
      rulingFormRestriction (LinearMap.ker A.toLin') t])
    (hb : b ∈ LinearMap.ker A.toLin') (hz : z ∈ LinearMap.ker A.toLin')
    (hsb : s ⬝ᵥ b = 1) (htb : t ⬝ᵥ b = 0)
    (hsz : s ⬝ᵥ z = 0) (htz : t ⬝ᵥ z = 1)
    (v : Fin n → E) (hv : A.map (algebraMap F E) *ᵥ v = 0) :
    ∀ i, v i = algebraMap F E (b i) * ((fun j => algebraMap F E (s j)) ⬝ᵥ v) +
      algebraMap F E (z i) * ((fun j => algebraMap F E (t j)) ⬝ᵥ v) :=
  matrix_kernel_coordinate_form_span_after_extension A s t b z
    (ruling_coordinates_of_specified_dual_pair (LinearMap.ker A.toLin') hdim
      s t b z hpair hb hz hsb htb hsz htz) v hv

end DimensionFourDependence
