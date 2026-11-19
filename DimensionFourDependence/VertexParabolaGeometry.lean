import DimensionFourDependence.ParabolicFiberDerivation
import DimensionFourDependence.ParabolaFromAffineSquare

/-! # Actual vertex-parabola coordinates give a nondegenerate nonlinear parabola -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 800000

variable {E G : Type*} [Field E] [CharZero E] [Field G] [Algebra E G]

/-- A nonzero projected direction and nonzero vertex acceleration
are independent in the original four coordinate labels. -/
theorem vertex_parabola_direction_pair_independent
    (A : Fin 3 → E) (B C : E) (hC : C ≠ 0) (j : Fin 3) (hj : A j ≠ 0) :
    LinearIndependent E ![(Fin.snoc A B : Fin 4 → E),
      (Fin.snoc (0 : Fin 3 → E) C : Fin 4 → E)] := by
  rw [LinearIndependent.pair_iff]
  intro u v huv
  have hj' := congrFun huv j.castSucc
  have hlast := congrFun huv (Fin.last 3)
  have hu : u = 0 := by
    have he : u * A j = 0 := by
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        Fin.snoc_castSucc, mul_zero, add_zero] using hj'
    exact (mul_eq_zero.mp he).resolve_right hj
  have hv : v = 0 := by
    have he : v * C = 0 := by
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        Fin.snoc_last, hu, zero_mul, zero_add] using hlast
    exact (mul_eq_zero.mp he).resolve_right hC
  exact ⟨hu, hv⟩

/-- The same actual transcendental parameter, nonzero projected
direction and nonzero vertex coefficient construct a nondegenerate
parabola in all four source coordinates. -/
theorem actual_vertex_coordinates_construct_affine_parabola
    (t : G) (ht : Transcendental E t) (z : Fin 4 → G)
    (x A : Fin 3 → E) (w B C : E) (hC : C ≠ 0) (j : Fin 3) (hj : A j ≠ 0)
    (hx : ∀ i : Fin 3, z i.castSucc = algebraMap E G (x i) + algebraMap E G (A i) * t)
    (hw : z (Fin.last 3) = algebraMap E G w + algebraMap E G B * t + algebraMap E G C * t ^ 2) :
    LiesInAffineParabola (L := E) z := by
  refine ⟨Fin.snoc x w, Fin.snoc A B, Fin.snoc (0 : Fin 3 → E) C,
    vertex_parabola_direction_pair_independent A B C hC j hj, t, ht, ?_⟩
  intro i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simpa only [Fin.snoc_last] using hw
  · simpa only [Fin.snoc_castSucc, Pi.zero_apply, map_zero, zero_mul, add_zero] using hx k

/-- These same vertex-parabola coordinates cannot lie on an affine
line. Their actual separating derivation has a constant nonzero
projected derivative and nonzero second vertex derivative. -/
theorem actual_vertex_coordinates_not_affine_line
    (t : G) (ht : Transcendental E t) (z : Fin 4 → G)
    (x A : Fin 3 → E) (w B C : E) (hC : C ≠ 0) (j : Fin 3) (hj : A j ≠ 0)
    (hx : ∀ i : Fin 3, z i.castSucc = algebraMap E G (x i) + algebraMap E G (A i) * t)
    (hw : z (Fin.last 3) = algebraMap E G w + algebraMap E G B * t + algebraMap E G C * t ^ 2) :
    ¬ LiesInAffineLine (E := E) z := by
  letI : CharZero G := charZero_of_injective_algebraMap (algebraMap E G).injective
  obtain ⟨D, _hDt, hDx, _hDw, hDDw⟩ :=
    actual_parabolic_fiber_constructs_separating_derivation t ht z x A w B C hx hw
  rintro ⟨a, v, _hv, s, hs⟩
  have hDline (i : Fin 4) : D (z i) = algebraMap E G (v i) * D s := by
    rw [hs i]
    simp only [map_add, D.map_algebraMap, Derivation.leibniz, smul_eq_mul,
      zero_add, mul_zero, add_zero]
  have hjG : algebraMap E G (A j) ≠ 0 := (map_ne_zero (algebraMap E G)).mpr hj
  have hpair : algebraMap E G (A j) = algebraMap E G (v j.castSucc) * D s :=
    (hDx j).symm.trans (hDline j.castSucc)
  have hvj : algebraMap E G (v j.castSucc) ≠ 0 := by
    intro hz
    exact hjG (hpair.trans (by rw [hz, zero_mul]))
  have hDs : D s = algebraMap E G (A j / v j.castSucc) := by
    rw [map_div₀]
    apply (eq_div_iff hvj).mpr
    exact (mul_comm _ _).trans hpair.symm
  have hDDs : D (D s) = 0 := by rw [hDs, D.map_algebraMap]
  have hzero : D (D (z (Fin.last 3))) = 0 := by
    rw [hDline, D.leibniz, D.map_algebraMap, hDDs]
    simp only [smul_eq_mul, mul_zero, zero_mul, add_zero]
  have hC0 : algebraMap E G C ≠ 0 := (map_ne_zero (algebraMap E G)).mpr hC
  exact (mul_ne_zero (two_ne_zero : (2 : G) ≠ 0) hC0) (hDDw.symm.trans hzero)

end DimensionFourDependence
