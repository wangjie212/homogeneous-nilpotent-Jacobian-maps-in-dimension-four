import DimensionFourDependence.LineChartBaseChange

/-! # The universal family over an original-field line-chart component

Quotient the matrix parameter ring by a component prime and retain the
two coordinates along the graph line. The resulting polynomial algebra
carries the universal image coordinates. Every extension-field line point
specializes this universal family, including its point on the line.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K]

/-- The graph coordinate forms over the quotient parameter ring of a component. -/
noncomputable def componentGraphLineCoordinate (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K)) :
    Fin 4 → MvPolynomial (Fin 2) (MvPolynomial (Fin 2 × Fin 2) K ⧸ Q) :=
  ![X 0, X 1,
    ∑ j, C (Ideal.Quotient.mk Q (X (0, j))) * X j,
    ∑ j, C (Ideal.Quotient.mk Q (X (1, j))) * X j]

/-- The universal incidence map in the original output-coordinate order. -/
noncomputable def componentLineIncidenceHom (p : Equiv.Perm (Fin 4))
    (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K)) :
    MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 2) (MvPolynomial (Fin 2 × Fin 2) K ⧸ Q) :=
  aeval (fun i => componentGraphLineCoordinate Q (p.symm i))

/-- Restriction followed by quotienting the parameter coefficients is the universal incidence map. -/
theorem componentLineIncidenceHom_restriction (p : Equiv.Perm (Fin 4))
    (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K)) (R : MvPolynomial (Fin 4) K) :
    componentLineIncidenceHom p Q R = MvPolynomial.map (Ideal.Quotient.mk Q)
      (universalGraphLineRestriction (rename p.symm R)) := by
  let s := MvPolynomial.mapAlgHom (σ := Fin 2) (Ideal.Quotient.mkₐ K Q)
  have hcoords : (fun i => s (universalGraphLineCoordinate (F := K) i)) =
      componentGraphLineCoordinate Q := by
    funext i
    fin_cases i <;> simp [s, mapAlgHom_apply, universalGraphLineCoordinate, componentGraphLineCoordinate]
  calc
    _ = aeval (componentGraphLineCoordinate Q) (rename p.symm R) := by
      rw [aeval_rename]
      rfl
    _ = s (aeval (universalGraphLineCoordinate (F := K)) (rename p.symm R)) := by
      rw [comp_aeval_apply, hcoords]
    _ = _ := rfl

/-- Every component of the chart's coefficient equations yields a universal
family lying on the original hypersurface equation. -/
theorem componentLineIncidenceHom_equation_zero (R : MvPolynomial (Fin 4) K)
    (p : Equiv.Perm (Fin 4)) (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K))
    (hQ : graphLineEquationIdeal (rename p.symm R) ≤ Q) : componentLineIncidenceHom p Q R = 0 := by
  classical
  rw [componentLineIncidenceHom_restriction]
  apply MvPolynomial.ext
  intro m
  rw [coeff_map]
  change Ideal.Quotient.mk Q ((universalGraphLineRestriction (rename p.symm R)).coeff m) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  by_cases hm : m ∈ (universalGraphLineRestriction (rename p.symm R)).support
  · apply hQ
    exact Ideal.subset_span (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  · rw [notMem_support_iff.mp hm]
    exact Q.zero_mem

variable {E : Type*} [Field E] [Algebra K E]

/-- Evaluation of the quotient parameter ring at a component's extension-field point. -/
noncomputable def componentLineParameterEvaluation (B : Matrix (Fin 2) (Fin 2) E)
    (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K))
    (hQ : Q ≤ (extendedLineChartPrime (K := K) B).asIdeal) :
    (MvPolynomial (Fin 2 × Fin 2) K ⧸ Q) →ₐ[K] E :=
  Ideal.Quotient.liftₐ Q (extendedLineChartSpecialization (K := K) B) (fun _ hf => hQ hf)

/-- The quotient evaluation agrees with the original parameter evaluation on representatives. -/
theorem componentLineParameterEvaluation_mk (B : Matrix (Fin 2) (Fin 2) E)
    (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K))
    (hQ : Q ≤ (extendedLineChartPrime (K := K) B).asIdeal)
    (f : MvPolynomial (Fin 2 × Fin 2) K) :
    componentLineParameterEvaluation B Q hQ (Ideal.Quotient.mk Q f) =
      extendedLineChartSpecialization B f := rfl

/-- Evaluation of the universal family at both its matrix parameters and line coordinates. -/
noncomputable def componentLineIncidenceEvaluation (B : Matrix (Fin 2) (Fin 2) E)
    (u : Fin 2 → E) (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K))
    (hQ : Q ≤ (extendedLineChartPrime (K := K) B).asIdeal) :
    MvPolynomial (Fin 2) (MvPolynomial (Fin 2 × Fin 2) K ⧸ Q) →ₐ[K] E :=
  ((aeval u).restrictScalars K).comp (MvPolynomial.mapAlgHom (componentLineParameterEvaluation B Q hQ))

/-- The universal graph coordinates specialize to the actual graph point. -/
theorem componentGraphLineCoordinate_evaluate (B : Matrix (Fin 2) (Fin 2) E)
    (u : Fin 2 → E) (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K))
    (hQ : Q ≤ (extendedLineChartPrime (K := K) B).asIdeal) :
    (fun i => componentLineIncidenceEvaluation B u Q hQ (componentGraphLineCoordinate Q i)) =
      ![u 0, u 1, (B *ᵥ u) 0, (B *ᵥ u) 1] := by
  funext i
  fin_cases i <;> simp [componentLineIncidenceEvaluation, componentLineParameterEvaluation_mk,
    componentGraphLineCoordinate, extendedLineChartSpecialization, Matrix.mulVec, dotProduct]

/-- The entire incidence map specializes to evaluation at the represented four-coordinate point. -/
theorem componentLineIncidenceHom_evaluate (p : Equiv.Perm (Fin 4))
    (B : Matrix (Fin 2) (Fin 2) E) (u : Fin 2 → E)
    (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K))
    (hQ : Q ≤ (extendedLineChartPrime (K := K) B).asIdeal) (R : MvPolynomial (Fin 4) K) :
    componentLineIncidenceEvaluation B u Q hQ (componentLineIncidenceHom p Q R) =
      aeval (fun i => (![u 0, u 1, (B *ᵥ u) 0, (B *ᵥ u) 1] : Fin 4 → E) (p.symm i)) R := by
  unfold componentLineIncidenceHom
  rw [comp_aeval_apply]
  have he := componentGraphLineCoordinate_evaluate B u Q hQ
  have hepoint : (fun i => componentLineIncidenceEvaluation B u Q hQ
      (componentGraphLineCoordinate Q (p.symm i))) =
      (fun i => (![u 0, u 1, (B *ᵥ u) 0, (B *ᵥ u) 1] : Fin 4 → E) (p.symm i)) := by
    funext i
    exact congrFun he (p.symm i)
  rw [hepoint]

/-- Every point of a represented line has actual coordinates in its universal graph. -/
theorem hypersurfaceAtlasLine_point_coordinates
    (R : MvPolynomial (Fin 4) E) (s : hypersurfaceLineAtlas R) (O : Fin 4 → E)
    (hO : O ∈ hypersurfaceAtlasLine R s) :
    ∃ u : Fin 2 → E, O = fun i =>
      (![u 0, u 1, (s.2.val *ᵥ u) 0, (s.2.val *ᵥ u) 1] : Fin 4 → E) (s.1.symm i) := by
  obtain ⟨z, hz, hzO⟩ := hO
  obtain ⟨u, hu⟩ := (mem_graphLineFour s.2.val z).mp hz
  refine ⟨u, ?_⟩
  rw [← hzO, hu]
  rfl

end DimensionFourDependence
