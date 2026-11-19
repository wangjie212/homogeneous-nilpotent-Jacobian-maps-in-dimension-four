import DimensionFourDependence.PlanarBinarySlopeAlgebraicity
import DimensionFourDependence.HomogeneousEvaluationScaling

/-! # The zeros of a binary form are covered by the same constant lines over every extension -/

namespace DimensionFourDependence

open MvPolynomial

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- The finite set of slopes is constructed over the given closed
field and works for every coefficient extension. -/
theorem homogeneous_binary_zero_has_constant_slope_cover
    (P : MvPolynomial (Fin 2) K) {d : ℕ} (hP : P.IsHomogeneous d) (hne : P ≠ 0) :
    ∃ slopes : Finset K, ∀ (F : Type v) [Field F] [Algebra K F] (y z : F),
      aeval ![y, z] P = 0 → y = 0 ∨ ∃ c ∈ slopes, z = algebraMap K F c * y := by
  classical
  let q : Polynomial K := aeval ![1, Polynomial.X] P
  have hq : q ≠ 0 := homogeneous_binary_first_chart_nonzero P hne hP
  refine ⟨q.roots.toFinset, ?_⟩
  intro F _ _ y z hz
  by_cases hy : y = 0
  · exact Or.inl hy
  right
  let s := z / y
  have hs : aeval (![1, s] : Fin 2 → F) P = 0 := by
    have h := homogeneous_aeval_scale P hP (![1, s] : Fin 2 → F) y
    have he : (fun j : Fin 2 => y * (![1, s] : Fin 2 → F) j) = ![y, z] := by
      funext j
      fin_cases j
      · change y * 1 = y
        exact mul_one _
      · change y * (z / y) = z
        rw [mul_comm, div_mul_cancel₀ _ hy]
    rw [he, hz] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ hy)
  have hEval : Polynomial.aeval s q = 0 := (eval_binary_first_chart P s).trans hs
  have hroot : (q.map (algebraMap K F)).IsRoot s := by
    change (q.map (algebraMap K F)).eval s = 0
    rw [Polynomial.eval_map]
    exact hEval
  have hmem := (Polynomial.mem_roots (Polynomial.map_ne_zero (f := algebraMap K F) hq)).mpr hroot
  rw [(IsAlgClosed.splits q).roots_map (algebraMap K F)] at hmem
  obtain ⟨c, hc, hcs⟩ := Multiset.mem_map.mp hmem
  exact ⟨c, Multiset.mem_toFinset.mpr hc, (div_eq_iff hy).mp hcs.symm⟩

end DimensionFourDependence
