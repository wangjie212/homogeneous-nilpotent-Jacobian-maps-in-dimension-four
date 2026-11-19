import DimensionFourDependence.ProjectiveCoordinatePoint
import DimensionFourDependence.PointAdaptedCoordinates
import DimensionFourDependence.LinearPolynomialCoordinates
import DimensionFourDependence.AffineSubstitutionDegree

/-! # Choosing a degree-preserving monic projection direction

Over an infinite field, the top homogeneous component has a nonvanishing
direction. An actual linear automorphism sends the first coordinate axis
to that direction. Restriction to that axis then proves that the fiber
degree is the full original total degree, with no increase of degree.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k σ : Type*} [Field k]

/-- The top homogeneous component of a nonzero polynomial is nonzero. -/
theorem top_homogeneousComponent_ne_zero (f : MvPolynomial σ k) (hf : f ≠ 0) :
    homogeneousComponent f.totalDegree f ≠ 0 := by
  classical
  obtain ⟨d, hd, hdegree⟩ := Finset.exists_mem_eq_sup f.support (support_nonempty.mpr hf)
    (fun d => d.sum fun _ n => n)
  change f.totalDegree = d.sum (fun _ n => n) at hdegree
  have hddegree : d.degree = f.totalDegree := by
    simpa only [Finsupp.degree_apply, Finsupp.sum] using hdegree.symm
  intro hzero
  have h := congrArg (fun p : MvPolynomial σ k => p.coeff d) hzero
  rw [coeff_homogeneousComponent, ite_eq_left hddegree] at h
  exact (mem_support_iff.mp hd) (by simpa using h)

variable {m n : ℕ}

/-- Restriction to parametrized lines commutes with the actual linear
polynomial coordinate substitution. -/
theorem linearPolynomialPullback_projective_line
    (A : Matrix (Fin m) (Fin n) k) (z : Fin n → k) (f : MvPolynomial (Fin m) k) :
    projectivePointLineMap z (linearPolynomialPullback A f) =
      projectivePointLineMap (A *ᵥ z) f := by
  have h : (projectivePointLineMap z).comp (aeval (linearPolynomialMap A)) =
      projectivePointLineMap (A *ᵥ z) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, aeval_X]
    change projectivePointLineMap z (linearPolynomialMap A i) =
      projectivePointLineMap (A *ᵥ z) (X i)
    rw [projectivePointLineMap_homogeneous z (linearPolynomialMap_homogeneous A i),
      projectivePointLineMap_homogeneous _ (isHomogeneous_X (R := k) i), aeval_X]
    rw [congrFun (linearPolynomialMap_aeval A z) i]
  exact AlgHom.congr_fun h f

/-- Restricting to the first coordinate axis cannot have larger degree
than the degree in that original coordinate. -/
theorem projective_axis_line_natDegree_le_degreeOf_zero
    (f : MvPolynomial (Fin (n + 1)) k) :
    (projectivePointLineMap (Pi.single 0 (1 : k)) f).natDegree ≤ f.degreeOf 0 := by
  let axis : MvPolynomial (Fin (n + 1)) k →ₐ[k] Polynomial k :=
    (Polynomial.mapAlgHom (aeval (0 : Fin n → k))).comp (finSuccEquiv k n).toAlgHom
  have haxis : axis = projectivePointLineMap (Pi.single 0 (1 : k)) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [axis, projectivePointLineMap, gradeHom, finSuccEquiv_X_zero]
    · simp [axis, projectivePointLineMap, gradeHom, finSuccEquiv_X_succ]
  have hdegree : (axis f).natDegree ≤ (finSuccEquiv k n f).natDegree :=
    Polynomial.natDegree_map_le
  rw [natDegree_finSuccEquiv, haxis] at hdegree
  exact hdegree

variable [Infinite k]

/-- A nonzero polynomial over an infinite field admits an actual
invertible linear change for which the first fiber coordinate has its
full original total degree. This is the monic projection choice, and the
new equation remains nonzero with exactly the original degree. -/
theorem exists_linear_monic_projection_coordinates
    (f : MvPolynomial (Fin (n + 1)) k) (hf : f ≠ 0) :
    ∃ T : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k),
      let g := linearPolynomialPullback (LinearMap.toMatrix' T.toLinearMap) f
      g ≠ 0 ∧ g.totalDegree = f.totalDegree ∧ g.degreeOf 0 = g.totalDegree := by
  classical
  let H := homogeneousComponent f.totalDegree f
  have hH : H ≠ 0 := top_homogeneousComponent_ne_zero f hf
  have hexists : ∃ v : Fin (n + 1) → k, v 0 ≠ 0 ∧ aeval v H ≠ 0 := by
    by_contra! h
    apply hH
    apply MvPolynomial.funext_set (fun _ => (Set.univ \ {(0 : k)}))
      (fun _ => Set.infinite_univ.sdiff (Set.finite_singleton 0))
    intro v hv
    have hv0 : v 0 ≠ 0 := by simpa only [Set.mem_singleton_iff] using (hv 0 (Set.mem_univ 0)).2
    simpa only [aeval_eq_eval, map_zero] using h v hv0
  obtain ⟨v, hv0, hvH⟩ := hexists
  have hv : v ≠ 0 := by
    intro hzero
    exact hv0 (congrFun hzero 0)
  let e₀ : Fin (n + 1) → k := Pi.single 0 1
  have he₀ : e₀ ≠ 0 := by
    intro hzero
    have h := congrFun hzero 0
    simp only [e₀, Pi.single_eq_same, Pi.zero_apply, one_ne_zero] at h
  obtain ⟨T, hT⟩ := exists_linearEquiv_map_nonzero_vector (F := k) e₀ v he₀ hv
  let A := LinearMap.toMatrix' T.toLinearMap
  let g := linearPolynomialPullback A f
  have hA : A *ᵥ e₀ = v := by
    change (Matrix.toLin' (LinearMap.toMatrix' T.toLinearMap)) e₀ = v
    rw [Matrix.toLin'_toMatrix']
    exact hT
  have hdegree : g.totalDegree ≤ f.totalDegree := by
    apply totalDegree_aeval_le_of_affine (linearPolynomialMap A) _ f
    intro i
    by_cases hi : linearPolynomialMap A i = 0
    · rw [hi]; simp
    · exact ((linearPolynomialMap_homogeneous A i).totalDegree hi).le
  have hcoeff : (projectivePointLineMap e₀ g).coeff f.totalDegree ≠ 0 := by
    rw [linearPolynomialPullback_projective_line, hA, projectivePointLineMap_coeff]
    exact hvH
  have hlower : f.totalDegree ≤ g.degreeOf 0 :=
    (Polynomial.le_natDegree_of_ne_zero hcoeff).trans
      (projective_axis_line_natDegree_le_degreeOf_zero g)
  have hgdegree : g.totalDegree = f.totalDegree :=
    hdegree.antisymm (hlower.trans (degreeOf_le_totalDegree g 0))
  have hgfull : g.degreeOf 0 = g.totalDegree := by
    apply (degreeOf_le_totalDegree g 0).antisymm
    exact hgdegree ▸ hlower
  have hg : g ≠ 0 := by
    intro hzero
    apply hcoeff
    rw [hzero, map_zero, Polynomial.coeff_zero]
  exact ⟨T, hg, hgdegree, hgfull⟩

end DimensionFourDependence
