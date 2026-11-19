import DimensionFourDependence.MatrixKernelDescent

/-! # A constant kernel direction makes an actual curve's quadratic acceleration zero -/

namespace DimensionFourDependence

open Matrix Module

set_option maxHeartbeats 3000000

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- If a rank-three Jacobian has a nonzero derivative-constant
kernel vector, one nonzero constant transverse tangent component forces
the entire actual curve's second derivative to vanish. -/
theorem rank_three_constant_kernel_direction_forces_zero_acceleration
    (N : Matrix (Fin 4) (Fin 4) F) (hrank : N.rank = 3)
    (D : Derivation K F F) (z u : Fin 4 → F)
    (hDz : N *ᵥ (fun i => D (z i)) = 0) (hu : u ≠ 0) (hNu : N *ᵥ u = 0)
    (hDu : ∀ i, D (u i) = 0)
    (j : Fin 4) (hDj : D (z j) ≠ 0) (hD2j : D (D (z j)) = 0) :
    ∀ i : Fin 4, D (D (z i)) = 0 := by
  let v : LinearMap.ker N.toLin' := ⟨u, hNu⟩
  have hv : v ≠ 0 := fun he => hu (congrArg Subtype.val he)
  obtain ⟨r, hr⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp
    (rank_three_matrix_kernel_finrank N hrank) ⟨(fun i => D (z i)), hDz⟩
  have hrep (i : Fin 4) : D (z i) = r * u i := by
    exact (congrFun (congrArg Subtype.val hr) i).symm
  have huj : u j ≠ 0 := by
    intro hz
    exact hDj (by rw [hrep j, hz, mul_zero])
  have hDr : D r = 0 := by
    have he := congrArg D (hrep j)
    rw [hD2j, D.leibniz, hDu j] at he
    simp only [smul_eq_mul, mul_zero, zero_add] at he
    exact (mul_eq_zero.mp he.symm).resolve_left huj
  intro i
  rw [hrep i, D.leibniz, hDr, hDu i]
  simp

end DimensionFourDependence
