import DimensionFourDependence.DirectionFieldLeadingCoefficient
import DimensionFourDependence.VertexPolynomialExpansion

/-! # The original vertex expansion supplies the whole leading coefficient family

Every nonzero original vertex coefficient retains its original
homogeneous degree and full direction-equation multiplicity. Its scalar
leading coefficient is constructed in the actual direction field.
Positive original vertex degree supplies a positive index in the
actual finite support.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E] {n : ℕ}

/-- The entire original homogeneous vertex expansion constructs all
nonzero coefficient-field scalars, exact original multiplicities and
affine leading bounds at once. -/
theorem original_parabolic_coefficient_family
    (A : Fin n → F) (Φ : MvPolynomial (Fin n) K) {δ : ℕ}
    (hΦ : Φ.IsHomogeneous δ) (hirr : Irreducible Φ)
    (hI : (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ})
    (P : MvPolynomial (Option (Fin n)) K) {e : ℕ}
    (hP0 : P ≠ 0) (hP : P.IsHomogeneous e) (hvertex : 0 < P.degreeOf none)
    (x : Fin n → E) :
    let Q := optionEquivLeft K (Fin n) P
    let m := fun j => multiplicity Φ (Q.coeff j)
    let f := fun j => aeval (fun i => Polynomial.C (x i) +
      Polynomial.C (algebraMap F E (A i)) * Polynomial.X) (Q.coeff j)
    let T := ∑ i, aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) * x i
    (∃ j ∈ Q.support, 0 < j) ∧
      ∃ c : ℕ → F, ∀ j ∈ Q.support,
        j ≤ e ∧ c j ≠ 0 ∧ m j ≤ e - j ∧ (f j).natDegree ≤ e - j - m j ∧
          (f j).coeff (e - j - m j) = algebraMap F E (c j) * T ^ m j := by
  classical
  dsimp only
  let Q := optionEquivLeft K (Fin n) P
  have hQ0 : Q ≠ 0 := by
    intro hz
    exact hP0 ((optionEquivLeft K (Fin n)).injective (hz.trans (map_zero _).symm))
  have hQdeg : Q.natDegree = P.degreeOf none := natDegree_optionEquivLeft K P
  have hJmem : P.degreeOf none ∈ Q.support :=
    hQdeg ▸ Polynomial.natDegree_mem_support_of_nonzero hQ0
  have hjbound (j : ℕ) (hj : j ∈ Q.support) : j ≤ e :=
    ((Polynomial.le_natDegree_of_mem_supp j hj).trans_eq hQdeg).trans
      ((degreeOf_le_totalDegree P none).trans hP.totalDegree_le)
  have hdata (j : ℕ) : ∃ c : F, j ∈ Q.support →
      c ≠ 0 ∧ multiplicity Φ (Q.coeff j) ≤ e - j ∧
      (aeval (fun i => Polynomial.C (x i) + Polynomial.C (algebraMap F E (A i)) * Polynomial.X)
        (Q.coeff j)).natDegree ≤ e - j - multiplicity Φ (Q.coeff j) ∧
      (aeval (fun i => Polynomial.C (x i) + Polynomial.C (algebraMap F E (A i)) * Polynomial.X)
        (Q.coeff j)).coeff (e - j - multiplicity Φ (Q.coeff j)) =
          algebraMap F E c *
            (∑ i, aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) * x i) ^ multiplicity Φ (Q.coeff j) := by
    by_cases hj : j ∈ Q.support
    · have hcoeff0 : Q.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
      have hhom : (Q.coeff j).IsHomogeneous (e - j) :=
        original_vertex_coefficient_isHomogeneous P hP j (hjbound j hj)
      obtain ⟨c, hc⟩ := direction_field_affine_leading_coefficient A Φ hΦ hirr hI
        (Q.coeff j) hcoeff0 hhom x
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => (hj h).elim⟩
  choose c hc using hdata
  refine ⟨⟨P.degreeOf none, hJmem, hvertex⟩, c, ?_⟩
  intro j hj
  exact ⟨hjbound j hj, hc j hj⟩

end DimensionFourDependence
