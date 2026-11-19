import DimensionFourDependence.ParabolaInfinityDirection
import DimensionFourDependence.ProjectiveBoundaryCoefficientComponent
import DimensionFourDependence.ScaledPlaneVertexAffineFiberBoundary

/-! # An actual fixed fourth-axis infinity point forces vertex-parabola coordinates -/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

/-- Membership of the original fourth-axis point in the actual
parabola closure forces exactly the original vertex-parabola shape.
The same transcendental parameter and same constant field are retained;
both nonzero directions are constructed from nondegeneracy. -/
theorem actual_parabola_fourth_axis_infinity_constructs_vertex_coordinates
    (z : Fin 4 → F) (hpara : LiesInAffineParabola (L := E) z)
    (hvertex : fourthAxisAffineInfinityPoint E ∈ projectiveClosureSet (L := E) z) :
    ∃ (t : F) (x A : Fin 3 → E) (w B C : E), Transcendental E t ∧ C ≠ 0 ∧ A ≠ 0 ∧
      (∀ i : Fin 3, z i.castSucc = algebraMap E F (x i) + algebraMap E F (A i) * t) ∧
      z (Fin.last 3) = algebraMap E F w + algebraMap E F B * t + algebraMap E F C * t ^ 2 := by
  classical
  obtain ⟨a, b, c, hbc, t, ht, hz⟩ := hpara
  let v : Fin 4 → E := Fin.snoc (0 : Fin 3 → E) 1
  have hv : v ≠ 0 := by
    intro hzero
    have he := congrFun hzero (Fin.last 3)
    exact one_ne_zero (by simpa only [v, Fin.snoc_last, Pi.zero_apply] using he)
  have hpoint : projectiveFieldPoint (E := E) (fun j : Option (Fin 4) => j.elim 0 v)
      (by intro h; exact hv (funext (fun i => congrFun h (some i)))) ∈
        projectiveClosureSet (L := E) z := by
    have hself := projectiveFieldPoint_self_eq_coordinatePoint
      (fun j : Option (Fin 4) => j.elim 0 v)
      (by intro h; exact hv (funext (fun i => congrFun h (some i))))
    rw [hself]
    exact hvertex
  obtain ⟨r, hr, hrep⟩ := actual_parabola_infinity_direction_multiple_quadratic_direction
    z a b c hbc t hz v hv hpoint
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hrep
  have hc (i : Fin 3) : c i.castSucc = 0 := by
    have he : r * c i.castSucc = 0 := by
      simpa only [v, Fin.snoc_castSucc, Pi.zero_apply] using (hrep i.castSucc).symm
    exact (mul_eq_zero.mp he).resolve_left hr
  have hclast : c (Fin.last 3) ≠ 0 := by
    intro hc0
    have he := hrep (Fin.last 3)
    simp only [v, Fin.snoc_last, hc0, mul_zero] at he
    exact one_ne_zero he
  have hA : (fun i : Fin 3 => b i.castSucc) ≠ 0 := by
    intro hzero
    have hb (i : Fin 3) : b i.castSucc = 0 := congrFun hzero i
    have hblast : b (Fin.last 3) ≠ 0 := by
      intro hb0
      apply hbc.ne_zero 0
      change b = 0
      funext i
      refine Fin.lastCases hb0 (fun j => hb j) i
    apply (LinearIndependent.pair_iff' (by simpa using hbc.ne_zero 0)).mp hbc
      (c (Fin.last 3) / b (Fin.last 3))
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact div_mul_cancel₀ _ hblast
    · simp only [Pi.smul_apply, smul_eq_mul, hb, hc, mul_zero]
  refine ⟨t, (fun i => a i.castSucc), (fun i => b i.castSucc),
    a (Fin.last 3), b (Fin.last 3), c (Fin.last 3), ht, hclast, hA, ?_, hz (Fin.last 3)⟩
  intro i
  simpa only [hc, map_zero, zero_mul, add_zero] using hz i.castSucc

end DimensionFourDependence
