import DimensionFourDependence.AffineLineDerivation

/-! # A nonlinear actual affine fiber has a nonzero projected direction -/

namespace DimensionFourDependence

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

/-- If all projected affine coordinates are constant, the entire
actual four-coordinate point lies on the original vertical affine line. -/
theorem liesInAffineLine_of_constant_projected_coordinates
    (z : Fin 4 → F) (x : Fin 3 → E)
    (hx : ∀ i : Fin 3, z i.castSucc = algebraMap E F (x i)) :
    LiesInAffineLine (E := E) z := by
  refine ⟨(Fin.snoc x 0 : Fin 4 → E), (Fin.snoc 0 1 : Fin 4 → E), ?_, z (Fin.last 3), ?_⟩
  · intro hz
    have he := congrFun hz (Fin.last 3)
    simp only [Fin.snoc_last, Pi.zero_apply] at he
    exact one_ne_zero he
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Fin.snoc_last, map_zero, map_one, one_mul, zero_add]
    · simp only [Fin.snoc_castSucc, Pi.zero_apply, map_zero, zero_mul, add_zero]
      exact hx i

/-- A genuinely nonlinear original fiber with affine-linear projected
coordinates has a nonzero actual projected direction, without any
choice of a direction coordinate or tangent derivation. -/
theorem nonlinear_affine_fiber_projected_direction_ne_zero
    (z : Fin 4 → F) (hline : ¬ LiesInAffineLine (E := E) z)
    (x A : Fin 3 → E) (t : F)
    (hx : ∀ i : Fin 3, z i.castSucc = algebraMap E F (x i) + algebraMap E F (A i) * t) : A ≠ 0 := by
  intro hz
  apply hline
  apply liesInAffineLine_of_constant_projected_coordinates z x
  intro i
  rw [hx, show A i = 0 from congrFun hz i, map_zero, zero_mul, add_zero]

end DimensionFourDependence
