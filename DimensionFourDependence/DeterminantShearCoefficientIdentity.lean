import DimensionFourDependence.Tame

/-! # A coefficient-conjugacy calculation in an arbitrary commutative algebra -/

namespace DimensionFourDependence.DeterminantShear

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

/-- The unipotent coefficient change preserves the shear coordinates.
All algebra homomorphisms remain abstract during this calculation, so
the polynomial automorphism implementations need not be unfolded. -/
theorem coefficient_conjugacy_coordinate_identity
    (E F I : A →ₐ[K] A) (x : Fin 4 → A) (c p q : A)
    (hE : ∀ j, E (x j) = ![x 0, x 1 + c * x 0, x 2 + c * x 3, x 3] j)
    (hI : ∀ j, I (x j) = ![x 0, x 1 - c * x 0, x 2 - c * x 3, x 3] j)
    (hF : ∀ j, F (x j) = ![x 0 + x 3 * p, x 1 + x 2 * p, x 2, x 3] j)
    (hFc : F c = c) (hEc : E c = c) (hp : E p = q) :
    ∀ j, E (F (I (x j))) = ![x 0 + x 3 * q, x 1 + x 2 * q, x 2, x 3] j := by
  intro j
  rw [hI]
  fin_cases j <;> simp [map_add, map_sub, map_mul, hF, hE, hFc, hEc, hp] <;> ring

end DimensionFourDependence.DeterminantShear
