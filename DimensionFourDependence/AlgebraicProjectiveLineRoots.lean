import DimensionFourDependence.RulingScalarExtensionDensity
import DimensionFourDependence.HomogeneousProjectiveLine

/-! # Nongeneric normalized points on a projective line are algebraic

A nonzero homogeneous binary equation makes every projective coordinate
ratio of one of its roots algebraic. Graph-line coordinates are linear
combinations of the two binary coordinates. Fixing one original
coordinate to one therefore makes all four coordinates algebraic.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

variable {K E : Type u} [Field K] [Field E] [Algebra K E] [Infinite K]

omit [Infinite K] in
/-- Restricting a homogeneous polynomial to a linear graph preserves
its homogeneous degree, including identically zero restrictions. -/
theorem graphLineRestriction_isHomogeneous
    (B : Matrix (Fin 2) (Fin 2) K) (P : MvPolynomial (Fin 4) K)
    {d : ℕ} (hP : P.IsHomogeneous d) : (graphLineRestriction B P).IsHomogeneous d := by
  have hlinear : IsHomogMap (graphLineCoordinate B) 1 := by
    intro i
    fin_cases i
    · exact isHomogeneous_X (R := K) 0
    · exact isHomogeneous_X (R := K) 1
    · change (∑ j : Fin 2, C (B 0 j) * X j).IsHomogeneous 1
      apply IsHomogeneous.sum
      intro j _
      exact isHomogeneous_C_mul_X _ _
    · change (∑ j : Fin 2, C (B 1 j) * X j).IsHomogeneous 1
      apply IsHomogeneous.sum
      intro j _
      exact isHomogeneous_C_mul_X _ _
  change (aeval (graphLineCoordinate B) P).IsHomogeneous d
  simpa only [Nat.one_mul] using hP.aeval (graphLineCoordinate B) hlinear

/-- A nonzero homogeneous binary polynomial cannot vanish identically
on the affine chart with first coordinate one. -/
theorem homogeneous_binary_affine_chart_ne_zero
    (P : MvPolynomial (Fin 2) K) {d : ℕ} (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) :
    aeval (![1, Polynomial.X] : Fin 2 → Polynomial K) P ≠ 0 := by
  intro hz
  let O : Fin 2 → K := ![1, 0]
  let D : Fin 2 → K := ![0, 1]
  have hline : aeval (fun i => Polynomial.C (O i) + Polynomial.C (D i) * Polynomial.X) P = 0 := by
    have he : (fun i => Polynomial.C (O i) + Polynomial.C (D i) * Polynomial.X) =
        (![1, Polynomial.X] : Fin 2 → Polynomial K) := by
      funext i
      fin_cases i <;> simp [O, D]
    rw [he]
    exact hz
  apply hP0
  apply MvPolynomial.funext
  intro x
  change aeval x P = aeval x (0 : MvPolynomial (Fin 2) K)
  rw [map_zero]
  apply homogeneous_affine_line_span_contained P hP O D hline x
  have hO : O ∈ Submodule.span K (Set.range ![O, D]) := Submodule.subset_span ⟨0, rfl⟩
  have hD : D ∈ Submodule.span K (Set.range ![O, D]) := Submodule.subset_span ⟨1, rfl⟩
  have he : x = x 0 • O + x 1 • D := by
    funext i
    fin_cases i <;> simp [O, D]
  rw [he]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hO) (Submodule.smul_mem _ _ hD)

/-- Every root of a nonzero homogeneous binary equation has algebraic
projective coordinate ratios over the original coefficient field. -/
theorem homogeneous_binary_root_ratios_isAlgebraic
    (P : MvPolynomial (Fin 2) K) {d : ℕ} (hP : P.IsHomogeneous d) (hP0 : P ≠ 0)
    (v : Fin 2 → E) (hv : v ≠ 0) (hzero : aeval v P = 0) :
    ∃ a : Fin 2, v a ≠ 0 ∧ ∀ i, IsAlgebraic K (v i / v a) := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> assumption
    refine ⟨1, h1, ?_⟩
    intro i
    fin_cases i
    · change IsAlgebraic K (v 0 / v 1)
      rw [h0, zero_div]
      exact isAlgebraic_zero
    · change IsAlgebraic K (v 1 / v 1)
      rw [div_self h1]
      exact isAlgebraic_one
  · have ht : IsAlgebraic K (v 1 / v 0) := by
      by_contra hn
      let Q : Polynomial K := aeval (![1, Polynomial.X] : Fin 2 → Polynomial K) P
      have hQ : Q ≠ 0 := homogeneous_binary_affine_chart_ne_zero P hP hP0
      have hchart : aeval (![1, v 1 / v 0] : Fin 2 → E) P = 0 := by
        have he := homogeneous_aeval_scale P hP (![1, v 1 / v 0] : Fin 2 → E) (v 0)
        have hcoords : (fun i => v 0 * (![1, v 1 / v 0] : Fin 2 → E) i) = v := by
          funext i
          fin_cases i
          · simp
          · exact mul_div_cancel₀ _ h0
        rw [hcoords, hzero] at he
        exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero d h0)
      have he : Polynomial.aeval (v 1 / v 0) Q = 0 := by
        change Polynomial.aeval (v 1 / v 0)
          (aeval (![1, Polynomial.X] : Fin 2 → Polynomial K) P) = 0
        rw [comp_aeval_apply]
        have heval : (fun i => Polynomial.aeval (v 1 / v 0)
            ((![1, Polynomial.X] : Fin 2 → Polynomial K) i)) =
            (![1, v 1 / v 0] : Fin 2 → E) := by
          funext i
          fin_cases i <;> simp
        rw [heval]
        exact hchart
      exact hQ ((transcendental_iff_injective.mp hn) (by simpa only [map_zero] using he))
    refine ⟨0, h0, ?_⟩
    intro i
    fin_cases i
    · change IsAlgebraic K (v 0 / v 0)
      rw [div_self h0]
      exact isAlgebraic_one
    · exact ht

/-- A normalized extension-field root of a genuine homogeneous
equation on a graph line has every original coordinate algebraic. -/
theorem normalized_graph_line_root_coordinates_isAlgebraic
    (p : Equiv.Perm (Fin 4)) (B : Matrix (Fin 2) (Fin 2) K)
    (P : MvPolynomial (Fin 4) K) {d : ℕ} (hP : P.IsHomogeneous d)
    (hrestrict : graphLineRestriction B (rename p.symm P) ≠ 0)
    (b : Fin 4 → E) (hb : b ∈ lineChartMemberLine p (B.map (algebraMap K E)))
    (hzero : aeval b P = 0) (a : Fin 4) (ha : b a = 1) :
    ∀ i, IsAlgebraic K (b i) := by
  obtain ⟨z, hz, hzb⟩ := hb
  obtain ⟨v, hv⟩ := (mem_graphLineFour _ _).mp hz
  have hcoords : b = fun i => (![v 0, v 1,
      (B.map (algebraMap K E) *ᵥ v) 0, (B.map (algebraMap K E) *ᵥ v) 1]) (p.symm i) := by
    rw [← hzb, hv]
    rfl
  have hv0 : v ≠ 0 := by
    intro he
    have hb0 : b = 0 := by
      rw [hcoords, he]
      simp only [Matrix.mulVec_zero, Pi.zero_apply]
      funext i
      generalize p.symm i = k
      fin_cases k <;> rfl
    rw [hb0, Pi.zero_apply] at ha
    exact zero_ne_one ha
  have hR : aeval v (graphLineRestriction B (rename p.symm P)) = 0 := by
    rw [graphLineRestriction_eval_extension, ← hcoords, hzero]
  obtain ⟨j, hj, hratio⟩ := homogeneous_binary_root_ratios_isAlgebraic
    (graphLineRestriction B (rename p.symm P)) (graphLineRestriction_isHomogeneous B _ hP.rename_isHomogeneous)
    hrestrict v hv0 hR
  have hscaled (i : Fin 4) : IsAlgebraic K (b i / v j) := by
    rw [hcoords]
    dsimp only
    generalize p.symm i = k
    fin_cases k
    · exact hratio 0
    · exact hratio 1
    · change IsAlgebraic K ((B.map (algebraMap K E) *ᵥ v) 0 / v j)
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, add_div, mul_div_assoc]
      exact ((isAlgebraic_algebraMap _).mul (hratio 0)).add
        ((isAlgebraic_algebraMap _).mul (hratio 1))
    · change IsAlgebraic K ((B.map (algebraMap K E) *ᵥ v) 1 / v j)
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, add_div, mul_div_assoc]
      exact ((isAlgebraic_algebraMap _).mul (hratio 0)).add
        ((isAlgebraic_algebraMap _).mul (hratio 1))
  have hvj : IsAlgebraic K (v j) := by
    have he := (hscaled a).inv
    simpa only [ha, one_div, inv_inv] using he
  intro i
  simpa only [div_mul_cancel₀ _ hj] using (hscaled i).mul hvj

end DimensionFourDependence
