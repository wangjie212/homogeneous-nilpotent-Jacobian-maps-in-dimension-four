import DimensionFourDependence.VertexParabolaFromInfinity
import DimensionFourDependence.ParabolaFieldEmbedding

/-! # Compatible embeddings retain the actual vertex-parabola coordinates -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 1000000

variable {L E F G : Type*} [Field L] [Field E] [Field F] [Field G]
    [Algebra L F] [Algebra E G] [IsAlgClosed E]

/-- An original parabola through the fourth-axis infinity point gives
the same vertex-parabola shape after a compatible nonlinear embedding. -/
theorem compatible_parabola_vertex_coordinates_of_nonlinear_image
    (f : F →+* G) (g : L →+* E)
    (hcomp : ∀ l : L, algebraMap E G (g l) = f (algebraMap L F l))
    (x : Fin 4 → F) (hpara : LiesInAffineParabola (L := L) x)
    (hvertex : fourthAxisAffineInfinityPoint L ∈ projectiveClosureSet (L := L) x)
    (hline : ¬ LiesInAffineLine (E := E) (f ∘ x)) :
    ∃ (t : G) (x₀ A : Fin 3 → E) (w B C : E), Transcendental E t ∧ C ≠ 0 ∧ A ≠ 0 ∧
      (∀ i : Fin 3, (f ∘ x) i.castSucc = algebraMap E G (x₀ i) + algebraMap E G (A i) * t) ∧
      (f ∘ x) (Fin.last 3) = algebraMap E G w + algebraMap E G B * t + algebraMap E G C * t ^ 2 := by
  obtain ⟨t, x₀, A, w, B, C, _ht, hC, hA, hx, hw⟩ :=
    actual_parabola_fourth_axis_infinity_constructs_vertex_coordinates x hpara hvertex
  have hxmap (i : Fin 3) : (f ∘ x) i.castSucc =
      algebraMap E G (g (x₀ i)) + algebraMap E G (g (A i)) * f t := by
    simpa only [map_add, map_mul, ← hcomp, Function.comp_apply] using congrArg f (hx i)
  have hwmap : (f ∘ x) (Fin.last 3) =
      algebraMap E G (g w) + algebraMap E G (g B) * f t + algebraMap E G (g C) * (f t) ^ 2 := by
    simpa only [map_add, map_mul, map_pow, ← hcomp, Function.comp_apply] using congrArg f hw
  have htmap : Transcendental E (f t) := by
    intro halg
    obtain ⟨r, hr⟩ := algebraic_value_preimage_of_isAlgClosed (f t) halg
    apply hline
    let point : Fin 4 → E := Fin.snoc
      (fun i => g (x₀ i) + g (A i) * r) (g w + g B * r + g C * r ^ 2)
    refine ⟨point, (fun _ => 1), ?_, 0, ?_⟩
    · intro hzero
      have he := congrFun hzero 0
      exact one_ne_zero he
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [point, Fin.snoc_last, map_add, map_mul, map_pow, mul_zero, add_zero, ← hr] using hwmap
      · simpa only [point, Fin.snoc_castSucc, map_add, map_mul, mul_zero, add_zero, ← hr] using hxmap i
  have hAmap : (g ∘ A) ≠ 0 := by
    intro hzero
    apply hA
    funext i
    apply g.injective
    simpa only [Function.comp_apply, Pi.zero_apply, map_zero] using congrFun hzero i
  exact ⟨f t, g ∘ x₀, g ∘ A, g w, g B, g C, htmap, (map_ne_zero g).mpr hC, hAmap, hxmap, hwmap⟩

end DimensionFourDependence
