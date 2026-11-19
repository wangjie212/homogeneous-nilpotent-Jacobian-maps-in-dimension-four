import DimensionFourDependence.LineComponentSeparation
import DimensionFourDependence.ConstantVertexGaussDimension
import DimensionFourDependence.LinearPolynomialCoordinates

/-! # Actual covering line families are neither coplanar nor concurrent

Uniform equations on all actual member lines vanish on the universal
incidence, whose kernel is the exact original image ideal. A common
hyperplane therefore gives component dependence. A common vertex gives
the original constant tangent-normal relation and forces Gauss dimension
at most one. These arguments derive both family obstructions.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

variable {K : Type*} [Field K] [IsAlgClosed K]
variable (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K)) [Q.IsPrime]

omit [IsAlgClosed K] [Q.IsPrime] in
/-- The actual member lines of a component lie on the original equation. -/
theorem lineComponentPoints_member_contained
    (R : MvPolynomial (Fin 4) K) (p : Equiv.Perm (Fin 4))
    (heq : graphLineEquationIdeal (rename p.symm R) ≤ Q)
    (B : Matrix (Fin 2) (Fin 2) K) (hB : B ∈ lineComponentPoints Q) :
    ∀ x ∈ lineChartMemberLine p B, aeval x R = 0 :=
  hypersurfaceAtlasLine_contained R
    ⟨p, ⟨B, lineComponentPoints_le_hypersurfaceLineChart _ Q heq hB⟩⟩

/-- A fixed nonzero hyperplane covector cannot annihilate all actual
lines in a covering component of a component-independent image. -/
theorem covering_line_component_no_constant_hyperplane
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hind : ¬ ComponentsDependent H)
    (p : Equiv.Perm (Fin 4))
    (hk : RingHom.ker (componentLineIncidenceHom p Q) = imageRelationIdeal H)
    (ν : Fin 4 → K) (hν : ν ≠ 0) :
    ¬ ∀ B ∈ lineComponentPoints Q, ∀ x ∈ lineChartMemberLine p B, ∑ i, ν i * x i = 0 := by
  intro hplane
  let L : MvPolynomial (Fin 4) K := ∑ i, MvPolynomial.C (ν i) * X i
  have hzero : componentLineIncidenceHom p Q L = 0 := by
    apply componentLineIncidenceHom_eq_zero_of_component_lines Q p L
    intro B hB x hx
    simpa only [L, map_sum, map_mul, aeval_C, aeval_X, Algebra.algebraMap_self_apply] using
      hplane B hB x hx
  have hmem : L ∈ RingHom.ker (componentLineIncidenceHom p Q) := hzero
  rw [hk] at hmem
  change aeval H L = 0 at hmem
  apply hind
  refine ⟨ν, hν, ?_⟩
  simpa only [L, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq,
    MvPolynomial.smul_eq_C_mul] using hmem

omit [IsAlgClosed K] in
/-- Every vector subspace of dimension at most three has a nonzero
constant covector annihilating it in four-dimensional coordinates. -/
theorem small_four_subspace_exists_annihilating_covector
    (T : Submodule K (Fin 4 → K)) (hT : finrank K T ≤ 3) :
    ∃ ν : Fin 4 → K, ν ≠ 0 ∧ ∀ x ∈ T, ∑ i, ν i * x i = 0 := by
  have hproper : T < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro ht
    rw [ht, finrank_top, Module.finrank_pi, Fintype.card_fin] at hT
    omega
  obtain ⟨f, hf, hTf⟩ := T.exists_dual_map_eq_bot_of_lt_top hproper inferInstance
  let g : (Fin 4 → K) →ₗ[K] (Fin 1 → K) := LinearMap.pi (fun _ => f)
  let A := LinearMap.toMatrix' g
  let ν : Fin 4 → K := fun i => A 0 i
  have heval (x : Fin 4 → K) : (∑ i, ν i * x i) = f x := by
    change (A *ᵥ x) 0 = f x
    have he : A *ᵥ x = g x := by
      change (Matrix.toLin' (LinearMap.toMatrix' g)) x = g x
      rw [Matrix.toLin'_toMatrix']
    exact congrFun he 0
  refine ⟨ν, ?_, ?_⟩
  · intro hz
    apply hf
    apply LinearMap.ext
    intro x
    rw [← heval, hz]
    simp
  · intro x hx
    rw [heval]
    have hm : f x ∈ T.map f := ⟨x, hx, rfl⟩
    rw [hTf, Submodule.mem_bot] at hm
    exact hm

/-- Actual member lines in a covering component cannot all lie in a fixed plane. -/
theorem covering_line_component_not_coplanar
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hind : ¬ ComponentsDependent H)
    (p : Equiv.Perm (Fin 4))
    (hk : RingHom.ker (componentLineIncidenceHom p Q) = imageRelationIdeal H) :
    ¬ ∃ T : Submodule K (Fin 4 → K), finrank K T ≤ 3 ∧
      ∀ B : lineComponentPoints Q, lineChartMemberLine p B.val ≤ T := by
  rintro ⟨T, hT, hcontain⟩
  obtain ⟨ν, hν, hνT⟩ := small_four_subspace_exists_annihilating_covector T hT
  apply covering_line_component_no_constant_hyperplane Q H hind p hk ν hν
  intro B hB x hx
  exact hνT x (hcontain ⟨B, hB⟩ hx)

variable [CharZero K]

omit [CharZero K] in
/-- A common constant vertex of all actual member lines gives the
original polynomial tangent-normal relation, with no generic-line
identity or uniform vertex relation left as a hypothesis. -/
theorem covering_line_component_common_vertex_normal_relation
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (heq : graphLineEquationIdeal (rename p.symm I.equation) ≤ Q)
    (hk : RingHom.ker (componentLineIncidenceHom p Q) = imageRelationIdeal H)
    (v : Fin 4 → K) (hv : ∀ B ∈ lineComponentPoints Q, v ∈ lineChartMemberLine p B) :
    ∑ i, MvPolynomial.C (v i) * imageRelationNormal H I.equation i = 0 := by
  let P : MvPolynomial (Fin 4) K := ∑ i, MvPolynomial.C (v i) * pderiv i I.equation
  have hzero : componentLineIncidenceHom p Q P = 0 := by
    apply componentLineIncidenceHom_eq_zero_of_component_lines Q p P
    intro B hB x hx
    have ht := contained_line_le_hypersurfaceTangentPlane I.equation x
      (lineChartMemberLine p B) hx (lineComponentPoints_member_contained Q _ p heq B hB) (hv B hB)
    change (∑ i, aeval x (pderiv i I.equation) * v i) = 0 at ht
    simpa only [P, map_sum, map_mul, aeval_C, Algebra.algebraMap_self_apply, mul_comm] using ht
  have hmem : P ∈ RingHom.ker (componentLineIncidenceHom p Q) := hzero
  rw [hk] at hmem
  change aeval H P = 0 at hmem
  simpa only [P, map_sum, map_mul, aeval_C, algebraMap_eq, imageRelationNormal] using hmem

/-- Gauss dimension two excludes every fixed nonzero vertex shared by
the actual member lines of a covering component. -/
theorem covering_line_component_no_constant_vertex
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 2)
    (p : Equiv.Perm (Fin 4))
    (heq : graphLineEquationIdeal (rename p.symm I.equation) ≤ Q)
    (hk : RingHom.ker (componentLineIncidenceHom p Q) = imageRelationIdeal H)
    (v : Fin 4 → K) (hv : v ≠ 0) :
    ¬ ∀ B ∈ lineComponentPoints Q, v ∈ lineChartMemberLine p B := by
  intro hvertex
  exact hv (gauss_dimension_two_no_constant_image_normal_vertex H hd hH hN hrank I hGauss v
    (covering_line_component_common_vertex_normal_relation Q H I p heq hk v hvertex))

/-- Actual member lines of a covering component with Gauss dimension
two cannot be concurrent in a common projective point. -/
theorem covering_line_component_not_concurrent
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 2)
    (p : Equiv.Perm (Fin 4))
    (heq : graphLineEquationIdeal (rename p.symm I.equation) ≤ Q)
    (hk : RingHom.ker (componentLineIncidenceHom p Q) = imageRelationIdeal H) :
    ¬ ∃ T : Submodule K (Fin 4 → K), finrank K T = 1 ∧
      ∀ B : lineComponentPoints Q, T ≤ lineChartMemberLine p B.val := by
  rintro ⟨T, hT, hcontain⟩
  obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := K) (M := T)).mp
    (show 0 < finrank K T by rw [hT]; omega)
  have hv0 : (v : Fin 4 → K) ≠ 0 := fun hz => hv (Subtype.ext hz)
  apply covering_line_component_no_constant_vertex Q H hd hH hN hrank I hGauss p heq hk v hv0
  intro B hB
  exact hcontain ⟨B, hB⟩ v.property

end DimensionFourDependence
