import DimensionFourDependence.GraphHilbert

/-! # Returning the Hilbert-degree bound to the original source coordinates

The verified hyperplane equation is solved as an affine graph. Its linear
projective embedding, and the recorded source-coordinate permutation,
preserve every homogeneous quotient dimension.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {L F : Type*} [Field L] [Field F] [Algebra L F] {n : ℕ}

/-- The affine graph expressed back in the original coordinate order. -/
noncomputable def sourceGraphPoint (p : Equiv.Perm (Fin (n + 1))) (c : L) (a : Fin n → L)
    (x : Fin n → F) : Fin (n + 1) → F := affineGraphPoint c a x ∘ p.symm

theorem projectiveHilbertFunction_sourceGraph (p : Equiv.Perm (Fin (n + 1)))
    (c : L) (a : Fin n → L) (x : Fin n → F) (d : ℕ) :
    projectiveHilbertFunction (projectiveConeIdeal (L := L) (sourceGraphPoint p c a x)) d =
      projectiveHilbertFunction (projectiveConeIdeal (L := L) x) d :=
  (projectiveHilbertFunction_reindex p.symm (affineGraphPoint c a x) d).trans
    (projectiveHilbertFunction_graph c a x d)

theorem curveHilbertDegree_sourceGraph (p : Equiv.Perm (Fin (n + 1)))
    (c : L) (a : Fin n → L) (x : Fin n → F) (d : ℕ) :
    HasCurveHilbertDegree (projectiveConeIdeal (L := L) (sourceGraphPoint p c a x)) d ↔
      HasCurveHilbertDegree (projectiveConeIdeal (L := L) x) d := by
  simp only [HasCurveHilbertDegree, projectiveHilbertFunction_sourceGraph]

/-- A hyperplane with unit last derivative is exactly the recorded affine graph. -/
theorem affine_hyperplane_eq_graph (P : MvPolynomial (Fin (n + 1)) L)
    (hP : P.totalDegree ≤ 1) (hlast : pderiv (Fin.last n) P = 1)
    (x : Fin (n + 1) → F) (hzero : aeval x P = 0) :
    x = affineGraphPoint (-P.coeff 0) (fun i : Fin n => -(pderiv i.castSucc P).coeff 0)
      (fun i : Fin n => x i.castSucc) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have he := affine_hyperplane_solve_last P hP hlast x hzero
    simpa [affineGraphPoint, map_neg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg] using he
  · simp [affineGraphPoint]

/-- Eliminating the last coordinate of this hyperplane preserves the projective Hilbert function. -/
theorem projectiveHilbertFunction_hyperplane (P : MvPolynomial (Fin (n + 1)) L)
    (hP : P.totalDegree ≤ 1) (hlast : pderiv (Fin.last n) P = 1)
    (x : Fin (n + 1) → F) (hzero : aeval x P = 0) (d : ℕ) :
    projectiveHilbertFunction (projectiveConeIdeal (L := L) x) d =
      projectiveHilbertFunction (projectiveConeIdeal (L := L) (fun i : Fin n => x i.castSucc)) d := by
  calc
    _ = projectiveHilbertFunction (projectiveConeIdeal (L := L)
        (affineGraphPoint (-P.coeff 0) (fun i : Fin n => -(pderiv i.castSucc P).coeff 0)
          (fun i : Fin n => x i.castSucc))) d :=
      congrArg (fun y : Fin (n + 1) → F => projectiveHilbertFunction (projectiveConeIdeal (L := L) y) d)
        (affine_hyperplane_eq_graph P hP hlast x hzero)
    _ = _ := projectiveHilbertFunction_graph _ _ _ d

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- The actual source closure in projective four-space and the projected
closure in projective three-space have identical Hilbert functions. -/
theorem fiber_witness_full_source_hilbert
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (W : FiberEquationWitness H) (d : ℕ) :
    projectiveHilbertFunction (projectiveConeIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc)))
      (rationalCoordinate (K := K) (n := 4))) d =
    projectiveHilbertFunction (projectiveConeIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc)))
      (fun i : Fin 3 => rationalCoordinate (K := K) (W.chart i.castSucc))) d := by
  have he := projectiveHilbertFunction_reindex
    (L := coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc)))
    W.chart (rationalCoordinate (K := K) (n := 4)) d
  exact he.symm.trans (projectiveHilbertFunction_hyperplane W.hyperplane W.hyperplane_degree
    W.hyperplane_last_derivative _ W.hyperplane_zero d)

/-- The original source-space closure has positive integral Hilbert degree at most six. -/
theorem fiber_witness_full_source_degree
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (W : ProjectiveFiberEquationWitness H) :
    ∃ d : ℕ, d ≤ 6 ∧ HasCurveHilbertDegree (projectiveConeIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc)))
      (rationalCoordinate (K := K) (n := 4))) d := by
  obtain ⟨d, hd6, hd⟩ := projective_fiber_witness_curve_hilbert_degree H hN hrank W
  refine ⟨d, hd6, ?_⟩
  simpa only [HasCurveHilbertDegree, fiber_witness_full_source_hilbert H W.affine.toFiberEquationWitness] using hd

end DimensionFourDependence
