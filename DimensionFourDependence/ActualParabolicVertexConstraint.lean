import DimensionFourDependence.ParabolicVertexLeadingCoefficient
import DimensionFourDependence.TranscendentalPolynomialParametrization

/-! # The original generic parabola supplies a proper direction equation

Constancy in the actual extension field is converted to an entire
polynomial identity using the actual transcendental parameter. The
highest original vertex coefficient then gives a fixed nonzero
homogeneous equation of positive degree for the projected direction.
Reindexing the original fourth coordinate as the vertex preserves both
the original polynomial evaluation and its vertex degree.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K E F sigma : Type*} [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra E F] [Algebra K F] [IsScalarTower K E F]

/-- The actual generic point's nonzero quadratic vertex coefficient
and polynomial constancy construct the original projected-direction equation. -/
theorem actual_parabolic_vertex_polynomial_direction_equation [Finite sigma]
    (P : MvPolynomial (Option sigma) K) (hP0 : P ≠ 0)
    {D : ℕ} (hP : P.IsHomogeneous D) (hJ : 0 < P.degreeOf none)
    (t : F) (ht : Transcendental E t) (z : Option sigma → F)
    (x A : sigma → E) (w0 B C : E) (hC : C ≠ 0)
    (hx : ∀ i, z (some i) = algebraMap E F (x i) + algebraMap E F (A i) * t)
    (hw : z none = algebraMap E F w0 + algebraMap E F B * t + algebraMap E F C * t ^ 2)
    (c : E) (hvalue : aeval z P = algebraMap E F c) :
    let Q := (optionEquivLeft K sigma P).coeff (P.degreeOf none)
    Q ≠ 0 ∧ Q.IsHomogeneous (D - P.degreeOf none) ∧ 0 < Q.totalDegree ∧ aeval A Q = 0 := by
  let w : Polynomial E := Polynomial.C w0 + Polynomial.C B * Polynomial.X +
    Polynomial.C C * Polynomial.X ^ 2
  let q : Option sigma → Polynomial E := fun j => j.elim w
    (fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X)
  have hq : ∀ j, Polynomial.aeval t (q j) = z j := by
    intro j
    cases j with
    | none => simpa [q, w] using hw.symm
    | some i => simpa [q] using (hx i).symm
  have hconstant := original_polynomial_parametrization_constant_of_transcendental t ht z q hq P c hvalue
  have hwdeg : w.natDegree ≤ 2 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le (by simp)
      exact Polynomial.natDegree_mul_le.trans (by simp)
    · exact (Polynomial.natDegree_C_mul_X_pow_le C 2)
  have hw2 : w.coeff 2 ≠ 0 := by simpa [w] using hC
  exact constant_parabolic_polynomial_constructs_proper_direction_equation
    P hP0 hP hJ x A w hwdeg hw2 c hconstant

/-- The original polynomial with its fourth variable distinguished
as the vertex coordinate; its coefficients remain original-field polynomials. -/
noncomputable def lastVertexPolynomial (P : MvPolynomial (Fin 4) K) :
    MvPolynomial (Option (Fin 3)) K := rename (finSuccEquiv' (Fin.last 3)) P

/-- Reindexing the vertex leaves the original source evaluation unchanged. -/
theorem lastVertexPolynomial_aeval (P : MvPolynomial (Fin 4) K) (z : Fin 4 → F) :
    aeval (fun j : Option (Fin 3) => j.elim (z (Fin.last 3)) (fun i => z i.castSucc))
      (lastVertexPolynomial P) = aeval z P := by
  rw [lastVertexPolynomial, aeval_rename]
  have hpoint : (fun j : Option (Fin 3) => j.elim (z (Fin.last 3)) (fun i => z i.castSucc)) ∘
      finSuccEquiv' (Fin.last 3) = z := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp
    · simp only [Function.comp_apply, finSuccEquiv'_below (Fin.castSucc_lt_last i), Option.elim_some]
  rw [hpoint]

/-- The distinguished vertex degree is exactly the original fourth-variable degree. -/
theorem lastVertexPolynomial_degree (P : MvPolynomial (Fin 4) K) :
    (lastVertexPolynomial P).degreeOf none = P.degreeOf (Fin.last 3) := by
  simpa [lastVertexPolynomial] using
    degreeOf_rename_of_injective (p := P) (finSuccEquiv' (Fin.last 3)).injective (Fin.last 3)

/-- An actual nonlinear fiber with projected affine-linear coordinates
has a nonzero projected direction. -/
theorem nonlinear_vertex_fiber_projected_direction_ne_zero
    (z : Fin 4 → F) (x A : Fin 3 → E) (t : F)
    (hx : ∀ i, z i.castSucc = algebraMap E F (x i) + algebraMap E F (A i) * t)
    (hline : ¬ LiesInAffineLine (E := E) z) : A ≠ 0 := by
  intro hA
  apply hline
  have hbase : (Fin.snoc x (0 : E) : Fin 4 → E) (3 : Fin 4) = 0 := by
    rw [show (3 : Fin 4) = Fin.last 3 from by decide]
    exact @Fin.snoc_last 3 (fun _ => E) 0 x
  have hdir : (Fin.snoc (0 : Fin 3 → E) 1 : Fin 4 → E) (3 : Fin 4) = 1 := by
    rw [show (3 : Fin 4) = Fin.last 3 from by decide]
    exact @Fin.snoc_last 3 (fun _ => E) 1 (0 : Fin 3 → E)
  refine ⟨Fin.snoc x 0, Fin.snoc (0 : Fin 3 → E) 1, ?_, z (Fin.last 3), ?_⟩
  · intro hv
    have h := congrFun hv (3 : Fin 4)
    change (Fin.snoc (0 : Fin 3 → E) 1 : Fin 4 → E) (3 : Fin 4) = 0 at h
    rw [hdir] at h
    exact one_ne_zero h
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [show (Fin.last 3 : Fin 4) = 3 from by decide]
      simp only [hbase, hdir, map_zero, map_one, zero_add, one_mul]
    · simpa [hA] using hx i

/-- In all four original source coordinates, a nonconstant vertex
invariant on an actual nonlinear parabola supplies a fixed proper
homogeneous plane equation for its nonzero projected direction. -/
theorem actual_four_coordinate_parabola_original_vertex_direction_equation
    (P : MvPolynomial (Fin 4) K) (hP0 : P ≠ 0)
    {D : ℕ} (hP : P.IsHomogeneous D) (hJ : 0 < P.degreeOf (Fin.last 3))
    (t : F) (ht : Transcendental E t) (z : Fin 4 → F)
    (x A : Fin 3 → E) (w0 B C : E) (hC : C ≠ 0)
    (hx : ∀ i, z i.castSucc = algebraMap E F (x i) + algebraMap E F (A i) * t)
    (hw : z (Fin.last 3) = algebraMap E F w0 + algebraMap E F B * t + algebraMap E F C * t ^ 2)
    (hline : ¬ LiesInAffineLine (E := E) z)
    (c : E) (hvalue : aeval z P = algebraMap E F c) :
    let Q := (optionEquivLeft K (Fin 3) (lastVertexPolynomial P)).coeff (P.degreeOf (Fin.last 3))
    A ≠ 0 ∧ Q ≠ 0 ∧ Q.IsHomogeneous (D - P.degreeOf (Fin.last 3)) ∧
      0 < Q.totalDegree ∧ aeval A Q = 0 := by
  have hP' : lastVertexPolynomial P ≠ 0 := by
    intro hz
    apply hP0
    apply (renameEquiv K (finSuccEquiv' (Fin.last 3))).injective
    exact hz.trans (map_zero _).symm
  have hhom : (lastVertexPolynomial P).IsHomogeneous D := hP.rename_isHomogeneous
  have hJ' : 0 < (lastVertexPolynomial P).degreeOf none := by
    rwa [lastVertexPolynomial_degree]
  have hvalue' : aeval (fun j : Option (Fin 3) => j.elim (z (Fin.last 3)) (fun i => z i.castSucc))
      (lastVertexPolynomial P) = algebraMap E F c :=
    (lastVertexPolynomial_aeval P z).trans hvalue
  have hresult := actual_parabolic_vertex_polynomial_direction_equation
    (lastVertexPolynomial P) hP' hhom hJ' t ht
    (fun j : Option (Fin 3) => j.elim (z (Fin.last 3)) (fun i => z i.castSucc))
    x A w0 B C hC hx hw c hvalue'
  rw [lastVertexPolynomial_degree] at hresult
  exact ⟨nonlinear_vertex_fiber_projected_direction_ne_zero z x A t hx hline, hresult⟩

end DimensionFourDependence
