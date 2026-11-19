import DimensionFourDependence.CoveringLineFamilyDensity
import DimensionFourDependence.SkewProjectiveLineQuadric
import DimensionFourDependence.StandardRulingQuadric

/-! # A covering family of transversals identifies the actual image quadric

Three skew lines give their determinant quadric in actual linear
coordinates. If a nonempty open part of an actual covering component
meets all three, its output points lie on that quadric and are dense in
the actual image. The original irreducible image equation must therefore
be quadratic and define precisely this quadric. Establishing the required
incidence between the two actual covering components remains separate.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

variable {K : Type*} [Field K]

/-- The determinant quadric written in arbitrary actual linear coordinates. -/
noncomputable def rulingPolynomialInCoordinates
    (e : (Fin 4 → K) ≃ₗ[K] ((Fin 2 → K) × (Fin 2 → K))) : MvPolynomial (Fin 4) K :=
  linearPolynomialPullback
    (LinearMap.toMatrix' ((fourCoordinateEquiv (F := K)).toLinearMap.comp e.toLinearMap))
    standardRulingPolynomial

/-- Its actual polynomial evaluation is the determinant in those coordinates. -/
theorem rulingPolynomialInCoordinates_eval
    (e : (Fin 4 → K) ≃ₗ[K] ((Fin 2 → K) × (Fin 2 → K))) (x : Fin 4 → K) :
    aeval x (rulingPolynomialInCoordinates e) = standardRulingQuadric (e x) := by
  rw [rulingPolynomialInCoordinates, linearPolynomialPullback_toMatrix_aeval]
  exact standardRulingPolynomial_eval_pair (e x)

/-- The coordinate-transported determinant equation is homogeneous quadratic. -/
theorem rulingPolynomialInCoordinates_homogeneous
    (e : (Fin 4 → K) ≃ₗ[K] ((Fin 2 → K) × (Fin 2 → K))) :
    (rulingPolynomialInCoordinates e).IsHomogeneous 2 :=
  linearPolynomialPullback_homogeneous _ _ standardRulingPolynomial_homogeneous

/-- It is a nonzero equation, since the actual linear coordinates are invertible. -/
theorem rulingPolynomialInCoordinates_ne_zero
    (e : (Fin 4 → K) ≃ₗ[K] ((Fin 2 → K) × (Fin 2 → K))) :
    rulingPolynomialInCoordinates e ≠ 0 := by
  intro hz
  have he := rulingPolynomialInCoordinates_eval e (e.symm (![1, 0], ![0, 1]))
  rw [hz, map_zero, e.apply_symm_apply] at he
  simp [standardRulingQuadric] at he

/-- Intersection of projective lines is the existence of a shared nonzero vector. -/
theorem line_not_disjoint_iff_nonzero_vector
    (L M : Submodule K (Fin 4 → K)) :
    ¬ Disjoint L M ↔ ∃ x : Fin 4 → K, x ≠ 0 ∧ x ∈ L ∧ x ∈ M := by
  constructor
  · intro h
    by_contra hn
    apply h
    apply Submodule.disjoint_def.mpr
    intro x hxL hxM
    by_contra hx
    exact hn ⟨x, hx, hxL, hxM⟩
  · rintro ⟨x, hx, hxL, hxM⟩ h
    exact hx (Submodule.disjoint_def.mp h x hxL hxM)

variable [CharZero K]

/-- A nonzero homogeneous quadratic image relation of a nonplanar
rank-three image is a nonzero scalar multiple of its actual defining equation. -/
theorem ImageRelationWitness.quadratic_relation_scalar_multiple
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (I : ImageRelationWitness H) (R : MvPolynomial (Fin 4) K)
    (hR : R.IsHomogeneous 2) (hR0 : R ≠ 0) (hvanish : aeval H R = 0) :
    I.degree = 2 ∧ ∃ c : K, c ≠ 0 ∧ R = MvPolynomial.C c * I.equation := by
  obtain ⟨q, hq⟩ := (I.relation_iff_dvd H hrank R).mp hvanish
  have hq0 : q ≠ 0 := by
    intro hz
    exact hR0 (by rw [hq, hz, mul_zero])
  have hdeg := congrArg MvPolynomial.totalDegree hq
  rw [hR.totalDegree hR0, totalDegree_mul_of_isDomain I.irreducible.ne_zero hq0,
    I.homogeneous.totalDegree I.irreducible.ne_zero] at hdeg
  have hIdeg : 2 ≤ I.degree := by
    have hp := I.degree_pos
    by_contra hn
    exact hind (I.dependent_of_degree_one H hd hH (by omega))
  have hqdeg : q.totalDegree = 0 := by omega
  have hqc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hqdeg
  refine ⟨by omega, q.coeff 0, ?_, ?_⟩
  · intro hc
    exact hq0 (by rw [hqc, hc, map_zero])
  · rw [hq, hqc, mul_comm]
    simp

variable [IsAlgClosed K]
variable (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K)) [Q.IsPrime]

/-- A nonempty open family of actual covering lines meeting three fixed
skew lines forces the actual image equation to be the smooth determinant
quadric in actual invertible linear coordinates. Only the incidence
between the two covering families remains an input to this final step. -/
theorem covering_transversals_identify_actual_image_quadric
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (I : ImageRelationWitness H) (p : Equiv.Perm (Fin 4))
    (hk : RingHom.ker (componentLineIncidenceHom p Q) = imageRelationIdeal H)
    (L₁ L₂ L₃ : Submodule K (Fin 4 → K))
    (hL₁ : finrank K L₁ = 2) (hL₂ : finrank K L₂ = 2) (hL₃ : finrank K L₃ = 2)
    (h₁₂ : Disjoint L₁ L₂) (h₁₃ : Disjoint L₁ L₃) (h₂₃ : Disjoint L₂ L₃) :
    letI := graphLineChartTopology K
    ∀ (U : Set (lineComponentPoints Q)), IsOpen U → U.Nonempty →
      (∀ B ∈ U, ¬ Disjoint (lineChartMemberLine p B.val) L₁ ∧
        ¬ Disjoint (lineChartMemberLine p B.val) L₂ ∧
        ¬ Disjoint (lineChartMemberLine p B.val) L₃) →
      I.degree = 2 ∧
        ∃ e : (Fin 4 → K) ≃ₗ[K] ((Fin 2 → K) × (Fin 2 → K)),
          ∀ x : Fin 4 → K, aeval x I.equation = 0 ↔ standardRulingQuadric (e x) = 0 := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) K) := graphLineChartTopology K
  intro U hU hUne hmeet
  obtain ⟨e, _, _, _, htrans, _⟩ := three_skew_projective_lines_quadric
    (by simp : finrank K (Fin 4 → K) = 4) L₁ L₂ L₃ hL₁ hL₂ hL₃ h₁₂ h₁₃ h₂₃
  have hzero : componentLineIncidenceHom p Q (rulingPolynomialInCoordinates e) = 0 := by
    apply componentLineIncidenceHom_eq_zero_of_open_component_lines Q p _ U hU hUne
    intro B hB x hx
    rw [rulingPolynomialInCoordinates_eval]
    exact htrans (lineChartMemberLine p B.val) (lineChartMemberLine_finrank p B.val)
      ((line_not_disjoint_iff_nonzero_vector _ _).mp (hmeet B hB).1)
      ((line_not_disjoint_iff_nonzero_vector _ _).mp (hmeet B hB).2.1)
      ((line_not_disjoint_iff_nonzero_vector _ _).mp (hmeet B hB).2.2) x hx
  have hmem : rulingPolynomialInCoordinates e ∈ RingHom.ker (componentLineIncidenceHom p Q) := hzero
  rw [hk] at hmem
  obtain ⟨hdeg, c, hc, heq⟩ := I.quadratic_relation_scalar_multiple H hd hH hrank hind _
    (rulingPolynomialInCoordinates_homogeneous e) (rulingPolynomialInCoordinates_ne_zero e) hmem
  refine ⟨hdeg, e, ?_⟩
  intro x
  rw [← rulingPolynomialInCoordinates_eval e x, heq]
  simp only [map_mul, aeval_C, Algebra.algebraMap_self_apply, mul_eq_zero, hc, false_or]

/-- The final quadric classification for two actual covering components
once their pairwise incidence is established. The skew triple, its
coordinate quadric and the density of the second component are all
constructed here from the original map and component equations. -/
theorem pairwise_incident_covering_components_identify_image_quadric
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 2) (p : Equiv.Perm (Fin 4))
    (heq : graphLineEquationIdeal (rename p.symm I.equation) ≤ Q)
    (hk : RingHom.ker (componentLineIncidenceHom p Q) = imageRelationIdeal H)
    (Q' : Ideal (MvPolynomial (Fin 2 × Fin 2) K)) [Q'.IsPrime]
    (p' : Equiv.Perm (Fin 4))
    (hk' : RingHom.ker (componentLineIncidenceHom p' Q') = imageRelationIdeal H)
    (hmeet : ∀ B : lineComponentPoints Q, ∀ D : lineComponentPoints Q',
      ¬ Disjoint (lineChartMemberLine p B.val) (lineChartMemberLine p' D.val)) :
    I.degree = 2 ∧
      ∃ e : (Fin 4 → K) ≃ₗ[K] ((Fin 2 → K) × (Fin 2 → K)),
        ∀ x : Fin 4 → K, aeval x I.equation = 0 ↔ standardRulingQuadric (e x) = 0 := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) K) := graphLineChartTopology K
  let : Nonempty (lineComponentPoints Q') := (lineComponentPoints_isIrreducible Q').nonempty.to_subtype
  obtain ⟨B, hB, D, hD, T, hT, hBD, hBT, hDT⟩ :=
    covering_line_component_skew_triple Q H hd hH hN hrank hind I hGauss p heq hk
  apply covering_transversals_identify_actual_image_quadric Q' H hd hH hrank hind I p' hk'
    (lineChartMemberLine p B) (lineChartMemberLine p D) (lineChartMemberLine p T)
    (lineChartMemberLine_finrank p B) (lineChartMemberLine_finrank p D)
    (lineChartMemberLine_finrank p T) hBD hBT hDT Set.univ isOpen_univ Set.univ_nonempty
  intro C _
  exact ⟨fun h => hmeet ⟨B, hB⟩ C h.symm,
    fun h => hmeet ⟨D, hD⟩ C h.symm, fun h => hmeet ⟨T, hT⟩ C h.symm⟩

end DimensionFourDependence
