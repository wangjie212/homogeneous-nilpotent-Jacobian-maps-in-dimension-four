import DimensionFourDependence.AffinePlaneGeneratorDegree
import DimensionFourDependence.QuadraticShearGraph
import DimensionFourDependence.AffineLineDerivation

/-! # Quadratic parametrization from an actual affine-linear square coordinate

If a transcendental coordinate and its square are both specified
affine-linear functions of the original coordinates, the degree-two
Hilbert bound constructs quadratic expressions for every original
coordinate. Actual nonlinearity makes the two coefficient directions
independent, giving a nondegenerate affine parabola.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {L F sigma : Type*} [Field L] [Field F] [Algebra L F]

/-- The actual square coordinate and the degree bound construct a
quadratic polynomial expression for every original coordinate. -/
theorem affine_square_coordinate_constructs_quadratic_expressions [Finite sigma]
    (x : sigma → F) (T U : MvPolynomial sigma L) (hT : T.totalDegree ≤ 1) (hU : U.totalDegree ≤ 1)
    (ht : Transcendental L (aeval x T)) (hUvalue : aeval x U = (aeval x T) ^ 2)
    {e : ℕ} (he : HasCurveHilbertDegree (projectiveConeIdeal (L := L) x) e) (hupper : e ≤ 2)
    (j : sigma) :
    ∃ a b c : L, x j = algebraMap L F a + algebraMap L F b * aeval x T +
      algebraMap L F c * (aeval x T) ^ 2 := by
  let p : Option Unit → MvPolynomial sigma L := fun k => k.elim (X j) (fun _ => T)
  let q : Option Unit → MvPolynomial sigma L := fun k => k.elim (X j + U) (fun _ => T)
  have hp : ∀ k, (p k).totalDegree ≤ 1 := by
    intro k
    cases k with
    | none => simp [p]
    | some u => exact hT
  have hq : ∀ k, (q k).totalDegree ≤ 1 := by
    intro k
    cases k with
    | none => exact (totalDegree_add (X j) U).trans (max_le (by simp) hU)
    | some u => exact hT
  obtain ⟨P, hP0, hPdeg, hPker⟩ := affine_plane_projection_exists_bounded_relation_generator x p hp ht he
  obtain ⟨Q, hQ0, hQdeg, hQker⟩ := affine_plane_projection_exists_bounded_relation_generator x q hq ht he
  have hpvalue : (fun k => aeval x (p k)) =
      (fun k : Option Unit => k.elim (x j) (fun _ => aeval x T)) := by
    funext k
    cases k with
    | none => exact aeval_X x j
    | some u => rfl
  have hqvalue : (fun k => aeval x (q k)) =
      (fun k : Option Unit => k.elim (x j + (aeval x T) ^ 2) (fun _ => aeval x T)) := by
    funext k
    cases k with
    | none => simp only [q, Option.elim_none, map_add, aeval_X, hUvalue]
    | some u => rfl
  rw [hpvalue] at hPker
  have hQvalue : aeval (fun k : Option Unit => k.elim (x j + (aeval x T) ^ 2) (fun _ => aeval x T)) Q = 0 := by
    rw [← hqvalue]
    change Q ∈ RingHom.ker (aeval (fun k => aeval x (q k)) : MvPolynomial (Option Unit) L →ₐ[L] F)
    rw [hQker]
    exact Ideal.subset_span (by simp)
  exact two_quadratic_shear_relations_construct_graph (aeval x T) (x j) ht P Q hP0 hQ0
    (hPdeg.trans hupper) (hQdeg.trans hupper) hPker hQvalue

variable {n : ℕ}

/-- The original coordinates have an actual nondegenerate affine
quadratic parametrization over their coefficient field. -/
def LiesInAffineParabola (x : Fin n → F) : Prop :=
  ∃ a b c : Fin n → L, LinearIndependent L ![b, c] ∧ ∃ t : F,
    Transcendental L t ∧ ∀ i,
      x i = algebraMap L F (a i) + algebraMap L F (b i) * t + algebraMap L F (c i) * t ^ 2

/-- Nonlinearity turns the constructed quadratic expressions into
two independent actual coefficient directions, rather than an affine line. -/
theorem affine_square_coordinate_constructs_parabola
    (x : Fin n → F) (T U : MvPolynomial (Fin n) L) (hT : T.totalDegree ≤ 1) (hU : U.totalDegree ≤ 1)
    (ht : Transcendental L (aeval x T)) (hUvalue : aeval x U = (aeval x T) ^ 2)
    {e : ℕ} (he : HasCurveHilbertDegree (projectiveConeIdeal (L := L) x) e) (hupper : e ≤ 2)
    (hline : ¬ LiesInAffineLine (E := L) x) : LiesInAffineParabola (L := L) x := by
  classical
  choose a b c hexp using affine_square_coordinate_constructs_quadratic_expressions x T U hT hU ht hUvalue he hupper
  let t := aeval x T
  have hb : b ≠ 0 := by
    intro hb0
    by_cases hc0 : c = 0
    · have hpoint : x = fun i => algebraMap L F (a i) := by
        funext i
        simpa only [hb0, hc0, Pi.zero_apply, map_zero, zero_mul, add_zero] using hexp i
      apply ht
      rw [hpoint]
      have heval : aeval (fun i => algebraMap L F (a i)) T = algebraMap L F (aeval a T) :=
        (comp_aeval_apply a (Algebra.ofId L F) T).symm
      rw [heval]
      exact isAlgebraic_algebraMap (aeval a T)
    · apply hline
      refine ⟨a, c, hc0, t ^ 2, ?_⟩
      intro i
      simpa only [hb0, Pi.zero_apply, map_zero, zero_mul, add_zero] using hexp i
  have hbc : LinearIndependent L ![b, c] := by
    apply (LinearIndependent.pair_iff' hb).mpr
    intro k hk
    apply hline
    refine ⟨a, b, hb, t + algebraMap L F k * t ^ 2, ?_⟩
    intro i
    have hc : c i = k * b i := by simpa only [Pi.smul_apply, smul_eq_mul] using (congrFun hk i).symm
    rw [hexp i, hc, map_mul]
    dsimp only [t]
    ring
  exact ⟨a, b, c, hbc, t, ht, hexp⟩

end DimensionFourDependence
