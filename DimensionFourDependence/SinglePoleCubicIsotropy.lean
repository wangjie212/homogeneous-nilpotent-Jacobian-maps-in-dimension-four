import DimensionFourDependence.SinglePoleResidueDirection
import DimensionFourDependence.CubicResidueDescent

/-! # The cubic isotropy equation extracted from a single pole

Normalize by the isotropic parameter, read the highest cubic equation
in the residue field, remove the radial shift and descend to constants.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {E F : Type*} [Field E] [CharZero E] [Field F] [Algebra E F] {n : ℕ}

/-- The single-pole argument yields the constant cubic self-equation,
without assuming the radial residue scalar belongs to the constants. -/
theorem single_pole_forces_constant_cubic_isotropy
    (V : ValuationSubring F) [Algebra E V] [IsScalarTower E V F]
    (x : Fin n → F) (Y Z W c : Fin n → E) (τ s t : F)
    (hx : ∀ i, x i = τ * algebraMap E F (Y i) + s * algebraMap E F (Z i) +
      t * algebraMap E F (W i) + algebraMap E F (c i))
    (hs : 1 < V.valuation s) (hτ : V.valuation τ ≤ V.valuation s) (ht : V.valuation t ≤ 1)
    (T : Matrix (Fin n) (Fin n) E) (C : Fin n → Fin n → Fin n → E)
    (h12 : ∀ i j k, C i j k = C j i k) (h23 : ∀ i j k, C i j k = C i k j)
    (hY : ∀ j, (∑ i, Y i * T i j) = 0)
    (hCY : ∀ j k, (∑ i, Y i * C i j k) = -T j k)
    (hZ : matrixBilinearPairing T Z Z = 0)
    (a : Fin n → E) (S : Matrix (Fin n) (Fin n) E) (k : E)
    (hCubic : aeval x (cubicFiberPolynomial a S C k) = 0) :
    tensorTrilinearPairing C Z Z Z = 0 := by
  obtain ⟨r, z, hnorm, hres0, hres⟩ := single_pole_radial_shift_residue V x Y Z W c τ s t hx hs hτ ht
  let κ := IsLocalRing.ResidueField V
  let π : V →ₐ[E] κ := IsScalarTower.toAlgHom E V κ
  have hz0 : algebraMap V F (z none) = s⁻¹ := by
    simpa only [Option.elim_none, mul_one] using hnorm none
  have hz (i : Fin n) : algebraMap V F (z (some i)) = s⁻¹ * x i := hnorm (some i)
  have hboundary := cubic_fiber_residue_direction_isotropic π
    (show Function.Injective (algebraMap V F) from Subtype.val_injective) x s⁻¹ z hz0 hz hres0 a S C k hCubic
  change tensorTrilinearPairing (fun i j l => algebraMap E κ (C i j l))
    (fun i => IsLocalRing.residue V (z (some i))) (fun i => IsLocalRing.residue V (z (some i)))
    (fun i => IsLocalRing.residue V (z (some i))) = 0 at hboundary
  have hfun : (fun i => IsLocalRing.residue V (z (some i))) =
      fun i => algebraMap E κ (Z i) + r * algebraMap E κ (Y i) := funext hres
  rw [hfun] at hboundary
  exact cubic_radial_residue_identity_descends T C h12 h23 Y Z hY hCY hZ r hboundary

end DimensionFourDependence
