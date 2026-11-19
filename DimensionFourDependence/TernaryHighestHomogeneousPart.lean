import DimensionFourDependence.TopPolynomialMatrixCoefficients
import DimensionFourDependence.AffineTriangularDivisibility

/-! # The nilpotent leading homogeneous perturbation in the ternary classification -/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] {n : ℕ}
local notation "R" => MvPolynomial (Fin n) K

theorem pderiv_homogeneousComponent_top (p : R) (i : Fin n) {d : ℕ} (hd : 0 < d) :
    pderiv i (homogeneousComponent d p) = homogeneousComponent (d - 1) (pderiv i p) := by
  classical
  ext m
  have hm : (m + Finsupp.single i 1).degree = m.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  rw [coeff_pderiv, coeff_homogeneousComponent, coeff_homogeneousComponent, coeff_pderiv, hm]
  by_cases h : m.degree = d - 1
  · have h' : m.degree + 1 = d := by omega
    simp only [if_pos h, if_pos h']
  · have h' : m.degree + 1 ≠ d := by omega
    simp only [if_neg h, if_neg h', zero_mul]

/-- The highest homogeneous component of a nilpotent-Jacobian map
has nilpotent Jacobian over the original coefficient field. -/
theorem highest_homogeneous_part_jacobian_isNilpotent
    (H : Fin n → R) {d : ℕ} (hd : 0 < d)
    (hdeg : ∀ i, (H i).totalDegree ≤ d) (hN : IsNilpotent (jac H)) :
    IsNilpotent (jac (fun i => homogeneousComponent d (H i))) := by
  have hD (i j : Fin n) : (jac H i j).totalDegree ≤ d - 1 := by
    change (pderiv j (H i)).totalDegree ≤ d - 1
    by_cases hz : pderiv j (H i) = 0
    · simp [hz]
    · have h := nonzero_polynomial_partial_totalDegree_succ_le (H i) j hz
      have h' := hdeg i
      omega
  have he : jac (fun i => homogeneousComponent d (H i)) = (jac H).map (homogeneousComponent (d - 1)) := by
    funext i j
    exact pderiv_homogeneousComponent_top (H i) j hd
  rw [he]
  exact top_homogeneous_component_matrix_isNilpotent (jac H) _ hD hN

/-- The nonzero leading homogeneous map in the normalized ternary
classification has positive degree and nilpotent Jacobian. -/
theorem normalized_ternary_map_constructs_highest_homogeneous_nilpotent
    (H : Fin 3 → MvPolynomial (Fin 3) K)
    (h0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (H i) = 0)
    (hind : ¬ComponentsDependent H) (hN : IsNilpotent (jac H)) :
    ∃ d : ℕ, 0 < d ∧ (∀ i, (H i).totalDegree ≤ d) ∧
      (fun i => homogeneousComponent d (H i)) ≠ 0 ∧
      IsHomogMap (fun i => homogeneousComponent d (H i)) d ∧
      IsNilpotent (jac (fun i => homogeneousComponent d (H i))) := by
  classical
  let d := Finset.univ.sup fun i : Fin 3 => (H i).totalDegree
  have hD (i : Fin 3) : (H i).totalDegree ≤ d :=
    Finset.le_sup (f := fun j : Fin 3 => (H j).totalDegree) (Finset.mem_univ i)
  have hn : H 0 ≠ 0 := by
    intro hz
    apply hind
    refine ⟨Pi.single 0 1, ?_, ?_⟩
    · intro he
      have h := congrFun he (0 : Fin 3)
      simpa using h
    · simp [Fin.sum_univ_succ, Pi.single_apply, hz]
  have hd : 0 < d := by
    by_contra! h
    have hdeg : (H 0).totalDegree = 0 := by have hd0 := hD 0; omega
    have hc := totalDegree_eq_zero_iff_eq_C.mp hdeg
    have hval := h0 0
    rw [hc, aeval_C, Algebra.algebraMap_self] at hval
    change (H 0).coeff 0 = 0 at hval
    exact hn (by rw [hc, hval, map_zero])
  obtain ⟨i, _, hi⟩ := (Finset.univ : Finset (Fin 3)).exists_mem_eq_sup Finset.univ_nonempty
    (fun j => (H j).totalDegree)
  have hdi : (H i).totalDegree = d := hi.symm
  have htop : homogeneousComponent d (H i) ≠ 0 := by
    have hi₀ : H i ≠ 0 := by
      intro hz
      rw [hz, totalDegree_zero] at hdi
      omega
    obtain ⟨m, hm, hmax⟩ := (H i).support.exists_mem_eq_sup (support_nonempty.mpr hi₀)
      (fun m => m.degree)
    have hmdeg : m.degree = d := by
      rw [← hdi]
      exact hmax.symm
    have hncoeff := mem_support_iff.mp hm
    intro hz
    have h := congrArg (fun p : MvPolynomial (Fin 3) K => p.coeff m) hz
    rw [coeff_homogeneousComponent, if_pos hmdeg] at h
    exact hncoeff (by simpa using h)
  refine ⟨d, hd, hD, ?_, fun i => homogeneousComponent_isHomogeneous _ _, ?_⟩
  · intro he
    exact htop (congrFun he i)
  · exact highest_homogeneous_part_jacobian_isNilpotent H hd hD hN

end DimensionFourDependence
