import DimensionFourDependence.FiniteTangentProportionality
import DimensionFourDependence.GenericFiberTangentNonvanishing
import DimensionFourDependence.ActualParabolicVertexConstraint

/-! # The actual generic parabolic fiber constructs finite tangent proportionality

Constancy of the original invariant at its actual transcendental fiber
parameter gives its entire polynomial identity. Independence is used at
the actual projected source point, not imposed on a chosen fiber base
point. The specified quadratic coefficient then constructs the actual
finite proportionality field.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K F E G : Type*} [Field K] [CharZero K] [Field F] [Field E] [Field G]
    [Algebra K F] [Algebra K E] [Algebra K G] [Algebra F E] [Algebra F G] [Algebra E G]
    [IsScalarTower K F E] [IsScalarTower K F G] [IsScalarTower K E G] [IsScalarTower F E G]

/-- An original invariant constant at the actual generic parabolic
point forces r to be a nonzero tangent multiple in its constructed
finite direction-field extension. Formal constancy and tangent
nonvanishing are both derived from the actual source point. -/
theorem actual_parabola_invariant_constructs_finite_tangent_proportionality
    (A : Fin 3 → F) (Φ : MvPolynomial (Fin 3) K) {δ : ℕ}
    (hΦ : Φ.IsHomogeneous δ) (hirr : Irreducible Φ)
    (hI : (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ})
    (P : MvPolynomial (Fin 4) K) {e : ℕ} (hP0 : P ≠ 0) (hP : P.IsHomogeneous e)
    (hvertex : 0 < P.degreeOf (Fin.last 3))
    (t : G) (ht : Transcendental E t) (z : Fin 4 → G) (x : Fin 3 → E) (w0 B C : E)
    (hx : ∀ i : Fin 3, z i.castSucc = algebraMap E G (x i) + algebraMap F G (A i) * t)
    (hw : z (Fin.last 3) = algebraMap E G w0 + algebraMap E G B * t + algebraMap E G C * t ^ 2)
    (hind : AlgebraicIndependent F (fun i : Fin 3 => z i.castSucc))
    (a : E) (hvalue : aeval z P = algebraMap E G a)
    (r : E) (hr : r ≠ 0) (κ : F) (hκ : κ ≠ 0) (hC : C = algebraMap F E κ / r) :
    let T := ∑ i : Fin 3, aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) * x i
    IsAlgebraic F (r / T) ∧ Module.Finite F (IntermediateField.adjoin F {r / T}) ∧
      ∃ u : IntermediateField.adjoin F {r / T}, u ≠ 0 ∧ r = (u : E) * T := by
  let w : Polynomial E := Polynomial.C w0 + Polynomial.C B * Polynomial.X + Polynomial.C C * Polynomial.X ^ 2
  let line : Fin 3 → Polynomial E := fun i => Polynomial.C (x i) +
    Polynomial.C (algebraMap F E (A i)) * Polynomial.X
  let q : Option (Fin 3) → Polynomial E := fun j => j.elim w line
  let z' : Option (Fin 3) → G := fun j => j.elim (z (Fin.last 3)) (fun i => z i.castSucc)
  have hq (j : Option (Fin 3)) : Polynomial.aeval t (q j) = z' j := by
    cases j with
    | none => simpa [q, w, z'] using hw.symm
    | some i => simpa [q, line, z', IsScalarTower.algebraMap_apply F E G] using (hx i).symm
  have hvalue' : aeval z' (lastVertexPolynomial P) = algebraMap E G a :=
    (lastVertexPolynomial_aeval P z).trans hvalue
  have hconstant : aeval q (lastVertexPolynomial P) = Polynomial.C a :=
    original_polynomial_parametrization_constant_of_transcendental t ht z' q hq
      (lastVertexPolynomial P) a hvalue'
  have hP'0 : lastVertexPolynomial P ≠ 0 := by
    intro hz
    exact hP0 ((renameEquiv K (finSuccEquiv' (Fin.last 3))).injective (hz.trans (map_zero _).symm))
  have hP'hom : (lastVertexPolynomial P).IsHomogeneous e := hP.rename_isHomogeneous
  have hvertex' : 0 < (lastVertexPolynomial P).degreeOf none := by
    rwa [lastVertexPolynomial_degree]
  have hwdeg : w.natDegree ≤ 2 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le (by simp)
      exact Polynomial.natDegree_mul_le.trans (by simp)
    · exact Polynomial.natDegree_C_mul_X_pow_le C 2
  have hwcoeff : w.coeff 2 = algebraMap F E κ / r := by simpa [w] using hC
  have hT := independent_fiber_source_constructs_nonzero_tangent_base_value A Φ hΦ hirr hI
    x t (fun i : Fin 3 => z i.castSucc) hx hind
  exact original_invariant_constructs_finite_tangent_proportionality A Φ hΦ hirr hI
    (lastVertexPolynomial P) hP'0 hP'hom hvertex' x hT w hwdeg a hconstant r hr κ hκ hwcoeff

end DimensionFourDependence
