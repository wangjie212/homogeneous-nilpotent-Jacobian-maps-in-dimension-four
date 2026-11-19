import DimensionFourDependence.TranscendentalSeparatingDerivation

/-! # Actual fiber lines and parabolas supply their own derivatives -/

namespace DimensionFourDependence

variable {E G : Type*} [Field E] [CharZero E] [Field G] [Algebra E G]

/-- Differentiating a projected affine fiber gives its actual constant direction. -/
theorem affine_fiber_coordinate_derivative
    (D : Derivation E G G) (t : G) (ht : D t = 1)
    (x A : E) (z : G) (hz : z = algebraMap E G x + algebraMap E G A * t) :
    D z = algebraMap E G A := by
  rw [hz]
  simp [Derivation.leibniz, ht]

/-- The actual vertex parabola has the stated slope and quadratic acceleration. -/
theorem parabolic_fiber_vertex_derivatives
    (D : Derivation E G G) (t : G) (ht : D t = 1)
    (w B C : E) (z : G)
    (hz : z = algebraMap E G w + algebraMap E G B * t + algebraMap E G C * t ^ 2) :
    D z = algebraMap E G B + 2 * algebraMap E G C * t ∧
      D (D z) = 2 * algebraMap E G C := by
  have hslope : D z = algebraMap E G B + 2 * algebraMap E G C * t := by
    rw [hz]
    simp [Derivation.leibniz, Derivation.leibniz_pow, ht]
    <;> ring
  have h2 : D (2 : G) = 0 := D.map_natCast 2
  exact ⟨hslope, by rw [hslope]; simp [Derivation.leibniz, ht, h2]⟩

/-- A transcendental actual fiber parameter constructs one derivation
realizing the entire affine direction, vertex slope and acceleration. -/
theorem actual_parabolic_fiber_constructs_separating_derivation
    (t : G) (ht : Transcendental E t) (z : Fin 4 → G)
    (x A : Fin 3 → E) (w B C : E)
    (hfirst : ∀ i : Fin 3, z i.castSucc = algebraMap E G (x i) + algebraMap E G (A i) * t)
    (hlast : z (Fin.last 3) = algebraMap E G w + algebraMap E G B * t + algebraMap E G C * t ^ 2) :
    ∃ D : Derivation E G G, D t = 1 ∧
      (∀ i : Fin 3, D (z i.castSucc) = algebraMap E G (A i)) ∧
      D (z (Fin.last 3)) = algebraMap E G B + 2 * algebraMap E G C * t ∧
      D (D (z (Fin.last 3))) = 2 * algebraMap E G C := by
  obtain ⟨D, hD⟩ := exists_derivation_apply_eq_one_of_transcendental t ht
  exact ⟨D, hD, fun i => affine_fiber_coordinate_derivative D t hD (x i) (A i) _ (hfirst i),
    parabolic_fiber_vertex_derivatives D t hD w B C _ hlast⟩

end DimensionFourDependence
