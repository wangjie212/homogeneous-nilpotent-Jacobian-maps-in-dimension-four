import DimensionFourDependence.GraphLineChartTopology

/-! # Polynomial equations for the lines on a hypersurface in a matrix chart

Substitute the universal graph line into the actual hypersurface equation.
Its finitely many binary-form coefficients are polynomial equations in the
four matrix entries. Their common zero set is precisely the line chart.
This constructs the chart and proves closedness; its covering components
and dimension are separate questions.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {F : Type*} [Field F]

/-- Linear forms parametrizing the graph line of a matrix. -/
noncomputable def graphLineCoordinate (B : Matrix (Fin 2) (Fin 2) F) :
    Fin 4 → MvPolynomial (Fin 2) F :=
  ![X 0, X 1, ∑ j, C (B 0 j) * X j, ∑ j, C (B 1 j) * X j]

/-- Restriction of a four-variable equation to the graph line. -/
noncomputable def graphLineRestriction (B : Matrix (Fin 2) (Fin 2) F)
    (R : MvPolynomial (Fin 4) F) : MvPolynomial (Fin 2) F := aeval (graphLineCoordinate B) R

/-- The universal graph line, over the polynomial ring in the matrix entries. -/
noncomputable def universalGraphLineCoordinate :
    Fin 4 → MvPolynomial (Fin 2) (MvPolynomial (Fin 2 × Fin 2) F) :=
  ![X 0, X 1, ∑ j, C (X (0, j)) * X j, ∑ j, C (X (1, j)) * X j]

/-- The universal binary form obtained by restricting the hypersurface equation. -/
noncomputable def universalGraphLineRestriction (R : MvPolynomial (Fin 4) F) :
    MvPolynomial (Fin 2) (MvPolynomial (Fin 2 × Fin 2) F) :=
  aeval (universalGraphLineCoordinate (F := F)) R

/-- Specializing the four parameters commutes with restriction to a line. -/
theorem universalGraphLineRestriction_specialize (B : Matrix (Fin 2) (Fin 2) F)
    (R : MvPolynomial (Fin 4) F) :
    MvPolynomial.map (aeval (fun ij : Fin 2 × Fin 2 => B ij.1 ij.2)).toRingHom
      (universalGraphLineRestriction R) = graphLineRestriction B R := by
  let f : MvPolynomial (Fin 2 × Fin 2) F →ₐ[F] F := aeval (fun ij => B ij.1 ij.2)
  let s : MvPolynomial (Fin 2) (MvPolynomial (Fin 2 × Fin 2) F) →ₐ[F]
      MvPolynomial (Fin 2) F := MvPolynomial.mapAlgHom f
  have hcoords : (fun i => s (universalGraphLineCoordinate (F := F) i)) = graphLineCoordinate B := by
    funext i
    fin_cases i <;>
      simp [universalGraphLineCoordinate, graphLineCoordinate, s, f, mapAlgHom_apply]
  change s (aeval (universalGraphLineCoordinate (F := F)) R) = _
  rw [comp_aeval_apply, hcoords]
  rfl

/-- The actual finite set of equations in the four matrix parameters. -/
noncomputable def graphLineEquationPolynomials (R : MvPolynomial (Fin 4) F) :
    Finset (MvPolynomial (Fin 2 × Fin 2) F) := by
  classical
  exact (universalGraphLineRestriction R).support.image (fun m => (universalGraphLineRestriction R).coeff m)

/-- The finite coefficient equations characterize identical vanishing on the line. -/
theorem graphLine_equations_iff_restriction_zero (B : Matrix (Fin 2) (Fin 2) F)
    (R : MvPolynomial (Fin 4) F) :
    (∀ P ∈ graphLineEquationPolynomials R, lineChartPolynomialValue B P = 0) ↔
      graphLineRestriction B R = 0 := by
  classical
  constructor
  · intro h
    apply MvPolynomial.ext
    intro m
    rw [← universalGraphLineRestriction_specialize, coeff_map]
    change lineChartPolynomialValue B ((universalGraphLineRestriction R).coeff m) = 0
    by_cases hm : m ∈ (universalGraphLineRestriction R).support
    · exact h _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
    · rw [notMem_support_iff.mp hm]
      exact map_zero _
  · intro h P hP
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hP
    have he := congrArg (fun Q : MvPolynomial (Fin 2) F => Q.coeff m) h
    rw [← universalGraphLineRestriction_specialize, coeff_map] at he
    change lineChartPolynomialValue B ((universalGraphLineRestriction R).coeff m) = 0 at he
    exact he

/-- The chart parameter space of lines contained in the given hypersurface. -/
noncomputable def hypersurfaceLineChart (R : MvPolynomial (Fin 4) F) :
    Set (Matrix (Fin 2) (Fin 2) F) := {B | graphLineRestriction B R = 0}

/-- The line parameter chart is cut out by its explicit finite polynomial equations. -/
theorem hypersurfaceLineChart_eq_zero_set (R : MvPolynomial (Fin 4) F) :
    hypersurfaceLineChart R = {B | ∀ P ∈ graphLineEquationPolynomials R,
      lineChartPolynomialValue B P = 0} := by
  ext B
  exact (graphLine_equations_iff_restriction_zero B R).symm

/-- The hypersurface's line chart is Zariski closed in the matrix parameter space. -/
theorem hypersurfaceLineChart_isClosed (R : MvPolynomial (Fin 4) F) :
    @IsClosed _ (graphLineChartTopology F) (hypersurfaceLineChart R) := by
  rw [hypersurfaceLineChart_eq_zero_set]
  exact lineChart_equations_isClosed {P | P ∈ graphLineEquationPolynomials R}

/-- Evaluation of the binary form is evaluation of the original equation
at the actual four-coordinate graph point. -/
theorem graphLineRestriction_eval (B : Matrix (Fin 2) (Fin 2) F)
    (R : MvPolynomial (Fin 4) F) (u : Fin 2 → F) :
    aeval u (graphLineRestriction B R) = aeval ![u 0, u 1, (B *ᵥ u) 0, (B *ᵥ u) 1] R := by
  unfold graphLineRestriction
  rw [comp_aeval_apply]
  have hcoords : (fun i => aeval u (graphLineCoordinate B i)) =
      ![u 0, u 1, (B *ᵥ u) 0, (B *ᵥ u) 1] := by
    funext i
    fin_cases i <;> simp [graphLineCoordinate, Matrix.mulVec, dotProduct]
  rw [hcoords]

/-- Each chart point is a genuine two-dimensional line on the hypersurface. -/
theorem hypersurfaceLineChart_line_contained (R : MvPolynomial (Fin 4) F)
    (B : Matrix (Fin 2) (Fin 2) F) (hB : B ∈ hypersurfaceLineChart R) :
    ∀ x ∈ graphLineFour B, aeval x R = 0 := by
  intro x hx
  obtain ⟨u, rfl⟩ := (mem_graphLineFour B x).mp hx
  rw [← graphLineRestriction_eval]
  change graphLineRestriction B R = 0 at hB
  rw [hB, map_zero]

/-- Over an infinite field, containment of all the line's points conversely
forces identical vanishing of the binary form, hence chart membership. -/
theorem hypersurfaceLineChart_mem_iff_line_contained [Infinite F]
    (R : MvPolynomial (Fin 4) F) (B : Matrix (Fin 2) (Fin 2) F) :
    B ∈ hypersurfaceLineChart R ↔ ∀ x ∈ graphLineFour B, aeval x R = 0 := by
  constructor
  · exact hypersurfaceLineChart_line_contained R B
  · intro h
    apply MvPolynomial.funext
    intro u
    change aeval u (graphLineRestriction B R) = aeval u (0 : MvPolynomial (Fin 2) F)
    rw [graphLineRestriction_eval, map_zero]
    exact h _ ((mem_graphLineFour B _).mpr ⟨u, rfl⟩)

end DimensionFourDependence
