import DimensionFourDependence.RectangularJacobianRank
import DimensionFourDependence.CoefficientCurveField

/-! # Jacobian rank equals output-field transcendence degree

A finite transcendence basis selected from the outputs gives the upper
Jacobian bound by the algebraic chain rule, and the lower bound by the
rectangular independent-family criterion. Its size is exactly the
transcendence degree of the actual generated output field.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
variable {K F : Type u} [Field K] [Field F] [Algebra K F] {r m : ℕ}

/-- Independent generators over which all outputs are algebraic give
the exact transcendence degree of the actual output field. -/
theorem outputField_trdeg_of_independent_algebraic_generators
    (Z : Fin r → F) (hZ : AlgebraicIndependent K Z) (H : Fin m → F)
    (hZH : Set.range Z ⊆ Set.range H)
    (hAlg : ∀ i, IsAlgebraic (IntermediateField.adjoin K (Set.range Z)) (H i)) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range H)) = r := by
  let B := IntermediateField.adjoin K (Set.range Z)
  let L := coefficientField (K := K) Z
  let M := IntermediateField.adjoin K (Set.range H)
  let : IsScalarTower K B L := IsScalarTower.of_algebraMap_eq (by intro k; rfl)
  let : FaithfulSMul K B := (faithfulSMul_iff_algebraMap_injective K B).mpr (algebraMap K B).injective
  let : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective B L).mpr (algebraMap B L).injective
  have hB : (r : Cardinal) = Algebra.trdeg K B := by
    calc
      _ = Algebra.trdeg K (FractionRing (MvPolynomial (Fin r) K)) := rationalSource_trdeg_eq.symm
      _ = _ := (rationalOutputEquiv Z hZ).trdeg_eq
  have hL : (r : Cardinal) = Algebra.trdeg K L := by
    have he := trdeg_add_eq (A := L) K B
    rw [show Algebra.trdeg B L = 0 from trdeg_eq_zero, add_zero] at he
    exact hB.trans he
  have hML : M ≤ L.restrictScalars K := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact mem_algebraicClosure_iff.mpr (hAlg i)
  let f : M →ₐ[K] L := IntermediateField.inclusion hML
  have hle : Algebra.trdeg K M ≤ r :=
    (trdeg_le_of_injective f f.injective).trans_eq hL.symm
  let z : Fin r → M := fun i => ⟨Z i, IntermediateField.subset_adjoin K _ (hZH ⟨i, rfl⟩)⟩
  have hz : AlgebraicIndependent K z := by
    apply AlgebraicIndependent.of_comp M.val
    exact hZ
  exact le_antisymm hle (by simpa using hz.lift_cardinalMk_le_trdeg)

variable [CharZero K] {n : ℕ}

omit [Field F] [Algebra K F] in
/-- The characteristic-zero Jacobian criterion for arbitrary finite
rational output families, using their actual generated output field. -/
theorem rationalJacobian_rank_eq_output_trdeg
    (H : Fin m → FractionRing (MvPolynomial (Fin n) K)) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range H)) = (rationalJacobian H).rank := by
  classical
  let F := FractionRing (MvPolynomial (Fin n) K)
  obtain ⟨S, hS⟩ := (AlgebraicIndependent.matroid K F).exists_isBasis (Set.range H)
  rcases AlgebraicIndependent.matroid_isBasis_iff.mp hS with ⟨hSind, hsub, hAlg⟩
  have hfin : S.Finite := (Set.finite_range H).subset hsub
  let : Fintype S := hfin.fintype
  let e := (Fintype.equivFin S).symm
  let f : S → Fin m := fun a => Classical.choose (hsub a.property)
  have hf (a : S) : H (f a) = (a : F) := Classical.choose_spec (hsub a.property)
  let Z : Fin (Fintype.card S) → F := fun i => H (f (e i))
  have hZ : AlgebraicIndependent K Z := by
    convert hSind.comp e e.injective using 1
    funext i
    exact hf (e i)
  have hrange : Set.range Z = S := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      change H (f (e i)) ∈ S
      rw [hf]
      exact (e i).property
    · intro hz
      refine ⟨e.symm ⟨z, hz⟩, ?_⟩
      change H (f (e (e.symm ⟨z, hz⟩))) = z
      rw [e.apply_symm_apply, hf]
  have hAlgZ (j : Fin m) : IsAlgebraic (IntermediateField.adjoin K (Set.range Z)) (H j) := by
    rw [hrange]
    exact IntermediateField.isAlgebraic_adjoin_iff.mpr (hAlg _ ⟨j, rfl⟩)
  have hu := rationalJacobian_rank_le_of_algebraic_outputs Z hZ H hAlgZ
  have hl : Fintype.card S ≤ (rationalJacobian H).rank := by
    have he := Matrix.rank_submatrix_le (rationalJacobian H) (fun i => f (e i)) id
    have hj : rationalJacobian Z = (rationalJacobian H).submatrix (fun i => f (e i)) id := rfl
    rw [← hj, rationalJacobian_rank_of_independent Z hZ] at he
    exact he
  have hr : (rationalJacobian H).rank = Fintype.card S := Nat.le_antisymm hu hl
  rw [hr]
  apply outputField_trdeg_of_independent_algebraic_generators Z hZ H _ hAlgZ
  rw [hrange]
  exact hsub

end DimensionFourDependence
