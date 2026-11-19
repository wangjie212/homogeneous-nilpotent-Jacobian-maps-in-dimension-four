import DimensionFourDependence.MovingPlanePointAlgebraicity

/-! # A genuine ternary tangent-line intersection is parameter-algebraic

The original three-coordinate covector equation is solved in its
specified nonzero pivot. A transcendental original normal-coordinate
ratio gives a genuine moving line. Reindexing the original ternary
equation then applies the proved nonzero binary restriction argument.
All normalized original coordinates, and their entire generated field,
are algebraic and finite over the line's coefficient field.
-/

namespace DimensionFourDependence

open MvPolynomial

universe u

variable {K : Type*} [Field K] [Infinite K]
    {L F : Type u} [Field L] [Field F] [Algebra K L] [Algebra L F]
    [Algebra K F] [IsScalarTower K L F]

/-- A fixed proper original homogeneous ternary equation and the
actual moving covector equation force every projective coordinate
ratio of their common direction to be algebraic over the ruling field. -/
theorem ternary_moving_line_original_point_ratios_isAlgebraic
    (nu : Fin 3 → L) (hnu : nu 2 ≠ 0) (hratio : Transcendental K (nu 0 / nu 2))
    (Q : MvPolynomial (Fin 3) K) (hQ0 : Q ≠ 0) {D : ℕ} (hQ : Q.IsHomogeneous D)
    (A : Fin 3 → F) (hA : A ≠ 0)
    (hline : algebraMap L F (nu 0) * A 0 + algebraMap L F (nu 1) * A 1 +
      algebraMap L F (nu 2) * A 2 = 0)
    (hzero : aeval A Q = 0) (j : Fin 3) (hj : A j ≠ 0) :
    ∀ i : Fin 3, IsAlgebraic L (A i / A j) := by
  let e : Fin 3 ≃ Option (Fin 2) := finSuccEquiv' (1 : Fin 3)
  have he0 : e 0 = some 0 := by decide
  have he1 : e 1 = none := by decide
  have he2 : e 2 = some 1 := by decide
  let P : MvPolynomial (Option (Fin 2)) K := rename e Q
  let v : Option (Fin 2) → F := fun o => o.elim (A 1) (![A 0, A 2] : Fin 2 → F)
  have hpoint : v ∘ e = A := by
    funext i
    fin_cases i <;> simp [v, he0, he1, he2]
  have hP0 : P ≠ 0 := by
    intro hz
    exact hQ0 ((renameEquiv K e).injective (hz.trans (map_zero _).symm))
  have hP : P.IsHomogeneous D := hQ.rename_isHomogeneous
  have hv0 : v ≠ 0 := by
    intro hz
    apply hA
    rw [← hpoint, hz]
    rfl
  have hvzero : aeval v P = 0 := by
    change aeval v (rename e Q) = 0
    rw [aeval_rename, hpoint, hzero]
  have hnuF : algebraMap L F (nu 2) ≠ 0 := by
    simpa only [map_zero] using (algebraMap L F).injective.ne hnu
  have hsolve : A 2 = algebraMap L F (-(nu 0 / nu 2)) * A 0 +
      algebraMap L F (-(nu 1 / nu 2)) * A 1 := by
    calc
      A 2 = -(algebraMap L F (nu 0) * A 0 + algebraMap L F (nu 1) * A 1) /
          algebraMap L F (nu 2) := by
        apply (eq_div_iff hnuF).mpr
        linear_combination hline
      _ = _ := by
        rw [map_neg, map_div₀, map_neg, map_div₀]
        ring
  have htrans : Transcendental K (-(nu 0 / nu 2)) := by
    intro halg
    exact hratio (by simpa only [neg_neg] using halg.neg)
  have hvj : v (e j) ≠ 0 := by
    have he : v (e j) = A j := congrFun hpoint j
    rwa [he]
  have halg := moving_plane_original_equation_all_chart_ratios_isAlgebraic
    (-(nu 0 / nu 2)) (-(nu 1 / nu 2)) htrans P hP0 hP v hv0 hsolve hvzero (e j) hvj
  intro i
  have hi : v (e i) = A i := congrFun hpoint i
  have hj' : v (e j) = A j := congrFun hpoint j
  have h := halg (e i)
  rwa [hi, hj'] at h

/-- The actual original projected-direction field is a finite
extension of the moving tangent line's specified ruling field. -/
theorem ternary_moving_line_original_direction_field_finite
    (nu : Fin 3 → L) (hnu : nu 2 ≠ 0) (hratio : Transcendental K (nu 0 / nu 2))
    (Q : MvPolynomial (Fin 3) K) (hQ0 : Q ≠ 0) {D : ℕ} (hQ : Q.IsHomogeneous D)
    (A : Fin 3 → F) (hA : A ≠ 0)
    (hline : algebraMap L F (nu 0) * A 0 + algebraMap L F (nu 1) * A 1 +
      algebraMap L F (nu 2) * A 2 = 0)
    (hzero : aeval A Q = 0) (j : Fin 3) (hj : A j ≠ 0) :
    Module.Finite L (IntermediateField.adjoin L (Set.range (fun i => A i / A j))) := by
  have halg := ternary_moving_line_original_point_ratios_isAlgebraic
    nu hnu hratio Q hQ0 hQ A hA hline hzero j hj
  apply IntermediateField.finiteDimensional_adjoin
  rintro z ⟨i, rfl⟩
  exact (halg i).isIntegral

end DimensionFourDependence
