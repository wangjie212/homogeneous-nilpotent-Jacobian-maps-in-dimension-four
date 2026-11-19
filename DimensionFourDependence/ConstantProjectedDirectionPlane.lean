import DimensionFourDependence.GeometricPlanarFiber
import DimensionFourDependence.ParabolaFieldEmbedding

/-! # A constant projected direction constructs the actual fixed direction plane

The horizontal lift of a nonzero original ternary vector and the fourth
axis are independent. A fiber with affine-linear projected coordinates
in that direction lies in an explicitly constructed translate of their
fixed plane. Over an algebraically closed original field, algebraic
projective direction ratios construct the required original-field vector.
-/

namespace DimensionFourDependence

variable {K E F : Type*} [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra E F] [Algebra K F] [IsScalarTower K E F]

/-- The original horizontal direction and the fourth axis give two
independent constant directions whenever the horizontal vector is nonzero. -/
theorem projected_direction_and_vertex_axis_linearIndependent
    (a : Fin 3 → K) (ha : a ≠ 0) :
    LinearIndependent K ![(Fin.snoc a 0 : Fin 4 → K), Fin.snoc (0 : Fin 3 → K) 1] := by
  let v : Fin 4 → K := Fin.snoc a 0
  let w : Fin 4 → K := Fin.snoc (0 : Fin 3 → K) 1
  have hw : w ≠ 0 := by
    intro hz
    have h := congrFun hz (Fin.last 3)
    change (Fin.snoc (0 : Fin 3 → K) 1 : Fin 4 → K) (Fin.last 3) = 0 at h
    rw [Fin.snoc_last] at h
    exact one_ne_zero h
  apply linearIndependent_fin2.mpr
  refine ⟨hw, ?_⟩
  intro c hc
  change c • w = v at hc
  apply ha
  funext i
  have h := congrFun hc i.castSucc
  simpa only [Fin.cons_zero, Fin.cons_one, v, w, Pi.smul_apply, smul_eq_mul,
    Fin.snoc_castSucc, Pi.zero_apply, mul_zero] using h.symm

/-- The entire actual fiber lies in a translate of the fixed plane
spanned by its original projected direction and the vertex axis. -/
theorem projected_affine_line_constructs_constant_vertex_plane_translate
    (z : Fin 4 → F) (x A : Fin 3 → E) (t : F)
    (hx : ∀ i : Fin 3, z i.castSucc = algebraMap E F (x i) + algebraMap E F (A i) * t)
    (a : Fin 3 → K) (c : E) (hA : ∀ i, A i = algebraMap K E (a i) * c) :
    LiesInConstantPlaneTranslate (E := E) (Fin.snoc a 0)
      (Fin.snoc (0 : Fin 3 → K) 1) z := by
  have hxlast : (Fin.snoc x (0 : E) : Fin 4 → E) (3 : Fin 4) = 0 := by
    rw [show (3 : Fin 4) = Fin.last 3 from by decide]
    exact @Fin.snoc_last 3 (fun _ => E) 0 x
  have hvlast : (Fin.snoc a (0 : K) : Fin 4 → K) (3 : Fin 4) = 0 := by
    rw [show (3 : Fin 4) = Fin.last 3 from by decide]
    exact @Fin.snoc_last 3 (fun _ => K) 0 a
  have hwlast : (Fin.snoc (0 : Fin 3 → K) 1 : Fin 4 → K) (3 : Fin 4) = 1 := by
    rw [show (3 : Fin 4) = Fin.last 3 from by decide]
    exact @Fin.snoc_last 3 (fun _ => K) 1 (0 : Fin 3 → K)
  refine ⟨Fin.snoc x 0, algebraMap E F c * t, z (Fin.last 3), ?_⟩
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [show (Fin.last 3 : Fin 4) = 3 from by decide]
    simp only [hxlast, hvlast, hwlast, map_zero, map_one, zero_mul, one_mul, zero_add]
  · have h := hx i
    rw [hA i, map_mul, ← IsScalarTower.algebraMap_apply K E F] at h
    simpa only [Fin.snoc_castSucc, Pi.zero_apply, map_zero, zero_mul, add_zero, mul_assoc] using h

/-- Algebraic projective ratios over an algebraically closed original
field construct the actual original horizontal vector and fixed plane. -/
theorem algebraic_projected_direction_constructs_original_constant_plane [IsAlgClosed K]
    (z : Fin 4 → F) (x A : Fin 3 → E) (t : F)
    (hx : ∀ i : Fin 3, z i.castSucc = algebraMap E F (x i) + algebraMap E F (A i) * t)
    (j : Fin 3) (hj : A j ≠ 0) (halg : ∀ i, IsAlgebraic K (A i / A j)) :
    ∃ a : Fin 3 → K, a j = 1 ∧
      LinearIndependent K ![(Fin.snoc a 0 : Fin 4 → K), Fin.snoc (0 : Fin 3 → K) 1] ∧
      LiesInConstantPlaneTranslate (E := E) (Fin.snoc a 0)
        (Fin.snoc (0 : Fin 3 → K) 1) z := by
  choose a ha using fun i => algebraic_value_preimage_of_isAlgClosed (A i / A j) (halg i)
  have haj : a j = 1 := by
    apply (algebraMap K E).injective
    exact (ha j).trans ((div_self hj).trans (map_one (algebraMap K E)).symm)
  have ha0 : a ≠ 0 := by
    intro hz
    have h := congrFun hz j
    rw [haj] at h
    exact one_ne_zero h
  have hA : ∀ i, A i = algebraMap K E (a i) * A j := by
    intro i
    exact ((eq_div_iff hj).mp (ha i)).symm
  exact ⟨a, haj, projected_direction_and_vertex_axis_linearIndependent a ha0,
    projected_affine_line_constructs_constant_vertex_plane_translate z x A t hx a (A j) hA⟩

end DimensionFourDependence
