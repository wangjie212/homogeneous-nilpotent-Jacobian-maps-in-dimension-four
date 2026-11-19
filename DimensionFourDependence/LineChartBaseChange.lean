import DimensionFourDependence.ProjectiveLineAtlasPoints
import DimensionFourDependence.LineChartNoetherian

/-! # Original-field equations and components of extension-field line parameters

The universal restriction specializes over any coefficient-field extension.
Thus a line-atlas point over the generic image field satisfies the finite
chart equations over the original field. Its evaluation kernel is a prime
containing those equations and lies over a minimal-prime chart component.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K]

/-- The actual ideal of coefficient equations of the hypersurface's line chart. -/
noncomputable def graphLineEquationIdeal (R : MvPolynomial (Fin 4) K) :
    Ideal (MvPolynomial (Fin 2 × Fin 2) K) :=
  Ideal.span {P | P ∈ graphLineEquationPolynomials R}

/-- The original-field coefficient ideal has finitely many minimal-prime components. -/
theorem graphLineEquationIdeal_finite_minimalPrimes (R : MvPolynomial (Fin 4) K) :
    (graphLineEquationIdeal R).minimalPrimes.Finite :=
  Ideal.finite_minimalPrimes_of_isNoetherianRing _ _

variable {E : Type*} [Field E] [Algebra K E]

/-- Specialization of the original-field matrix parameters in an extension field. -/
noncomputable def extendedLineChartSpecialization (B : Matrix (Fin 2) (Fin 2) E) :
    MvPolynomial (Fin 2 × Fin 2) K →ₐ[K] E := aeval (fun ij => B ij.1 ij.2)

/-- The original universal restriction specializes to the scalar-extended equation
on the extension-field graph line. -/
theorem universalGraphLineRestriction_specialize_extension
    (B : Matrix (Fin 2) (Fin 2) E) (R : MvPolynomial (Fin 4) K) :
    MvPolynomial.map (extendedLineChartSpecialization (K := K) B).toRingHom
      (universalGraphLineRestriction R) = graphLineRestriction B (MvPolynomial.map (algebraMap K E) R) := by
  let s : MvPolynomial (Fin 2) (MvPolynomial (Fin 2 × Fin 2) K) →ₐ[K]
      MvPolynomial (Fin 2) E := MvPolynomial.mapAlgHom (extendedLineChartSpecialization (K := K) B)
  have hcoords : (fun i => s (universalGraphLineCoordinate (F := K) i)) = graphLineCoordinate B := by
    funext i
    fin_cases i <;> simp [universalGraphLineCoordinate, graphLineCoordinate, s,
      extendedLineChartSpecialization, mapAlgHom_apply]
  change s (aeval (universalGraphLineCoordinate (F := K)) R) = _
  rw [comp_aeval_apply, hcoords]
  exact (aeval_map_algebra_extension R (graphLineCoordinate B)).symm

/-- Extension-field chart points satisfy exactly the original coefficient equations. -/
theorem extended_line_chart_equations_iff (B : Matrix (Fin 2) (Fin 2) E)
    (R : MvPolynomial (Fin 4) K) :
    (∀ P ∈ graphLineEquationPolynomials R, extendedLineChartSpecialization B P = 0) ↔
      B ∈ hypersurfaceLineChart (MvPolynomial.map (algebraMap K E) R) := by
  classical
  change _ ↔ graphLineRestriction B (MvPolynomial.map (algebraMap K E) R) = 0
  constructor
  · intro h
    apply MvPolynomial.ext
    intro m
    rw [← universalGraphLineRestriction_specialize_extension, coeff_map]
    change extendedLineChartSpecialization B ((universalGraphLineRestriction R).coeff m) = 0
    by_cases hm : m ∈ (universalGraphLineRestriction R).support
    · exact h _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
    · rw [notMem_support_iff.mp hm, map_zero]
  · intro h P hP
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hP
    have he := congrArg (fun Q : MvPolynomial (Fin 2) E => Q.coeff m) h
    rw [← universalGraphLineRestriction_specialize_extension, coeff_map] at he
    exact he

/-- The prime of original-field polynomial relations of an extension-field chart point. -/
noncomputable def extendedLineChartPrime (B : Matrix (Fin 2) (Fin 2) E) :
    PrimeSpectrum (MvPolynomial (Fin 2 × Fin 2) K) where
  asIdeal := RingHom.ker (extendedLineChartSpecialization (K := K) B)
  isPrime := RingHom.ker_isPrime _

/-- The evaluated prime lies on the original-field chart precisely when its
line is contained in the scalar-extended hypersurface. -/
theorem graphLineEquationIdeal_le_extendedPrime_iff
    (R : MvPolynomial (Fin 4) K) (B : Matrix (Fin 2) (Fin 2) E) :
    graphLineEquationIdeal R ≤ (extendedLineChartPrime (K := K) B).asIdeal ↔
      B ∈ hypersurfaceLineChart (MvPolynomial.map (algebraMap K E) R) := by
  unfold graphLineEquationIdeal
  rw [Ideal.span_le]
  exact extended_line_chart_equations_iff B R

/-- Every extension-field line parameter lies over an original-field minimal-prime component. -/
theorem extension_line_chart_point_exists_original_component
    (R : MvPolynomial (Fin 4) K) (B : Matrix (Fin 2) (Fin 2) E)
    (hB : B ∈ hypersurfaceLineChart (MvPolynomial.map (algebraMap K E) R)) :
    ∃ Q ∈ (graphLineEquationIdeal R).minimalPrimes,
      Q ≤ (extendedLineChartPrime (K := K) B).asIdeal := by
  let : (extendedLineChartPrime (K := K) B).asIdeal.IsPrime :=
    (extendedLineChartPrime (K := K) B).isPrime
  exact Ideal.exists_minimalPrimes_le ((graphLineEquationIdeal_le_extendedPrime_iff R B).mpr hB)

/-- An actual atlas point after extension belongs to a component of a
coordinate chart defined by the original equation over the original field. -/
theorem atlas_point_exists_original_field_component
    (R : MvPolynomial (Fin 4) K)
    (s : hypersurfaceLineAtlas (MvPolynomial.map (algebraMap K E) R)) :
    ∃ Q ∈ (graphLineEquationIdeal (rename s.1.symm R)).minimalPrimes,
      Q ≤ (extendedLineChartPrime (K := K) s.2.val).asIdeal := by
  apply extension_line_chart_point_exists_original_component
  simpa only [MvPolynomial.map_rename] using s.2.property

end DimensionFourDependence
