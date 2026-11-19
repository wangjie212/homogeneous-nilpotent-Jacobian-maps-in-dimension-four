import DimensionFourDependence.RelativelyClosedAlgebraicBaseChange

/-! # Compatible source and algebraic coefficients have one fraction-field realization

Relative closedness makes the algebraic source tensor a field. Its
universal realization is consequently injective and extends to the
specified fraction field, preserving every source value and coefficient.
-/

namespace DimensionFourDependence

open scoped TensorProduct

variable {C S L G : Type*} [Field C] [CharZero C] [Field S] [Field L] [Field G]
    [Algebra C S] [Algebra C L] [Algebra C G] [Algebra.IsAlgebraic C L]
    [IsDomain (S ⊗[C] L)]

set_option maxHeartbeats 2000000

/-- A compatible realization of a relatively closed source and its
algebraic coefficient extension constructs one actual injective
fraction-field homomorphism retaining both factors. -/
theorem relatively_closed_algebraic_source_tensor_constructs_fraction_realization
    (hclosed : algebraicClosure C S = ⊥) (f : S →ₐ[C] G) (g : L →ₐ[C] G) :
    ∃ φ : FractionRing (S ⊗[C] L) →ₐ[C] G,
      (∀ s : S, φ (algebraMap (S ⊗[C] L) (FractionRing (S ⊗[C] L)) (s ⊗ₜ[C] (1 : L))) = f s) ∧
      (∀ l : L, φ (algebraMap (S ⊗[C] L) (FractionRing (S ⊗[C] L)) ((1 : S) ⊗ₜ[C] l)) = g l) := by
  classical
  let δ : S ⊗[C] L →ₐ[C] G := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  have hfield := algebraic_tensor_isField_of_relatively_closed (L := L) hclosed
  have hinj : Function.Injective δ := by
    apply (injective_iff_map_eq_zero δ).mpr
    intro x hx
    by_contra hn
    obtain ⟨y, hy⟩ := hfield.mul_inv_cancel hn
    have he := congrArg δ hy
    rw [map_mul, hx, zero_mul, map_one] at he
    exact zero_ne_one he
  let φ : FractionRing (S ⊗[C] L) →ₐ[C] G := IsFractionRing.liftAlgHom hinj
  have hφ (x : S ⊗[C] L) : φ (algebraMap (S ⊗[C] L) (FractionRing (S ⊗[C] L)) x) = δ x := by
    exact IsFractionRing.lift_algebraMap hinj x
  refine ⟨φ, ?_, ?_⟩
  · intro s
    rw [hφ]
    simp [δ, Algebra.TensorProduct.lift_tmul]
  · intro l
    rw [hφ]
    simp [δ, Algebra.TensorProduct.lift_tmul]

end DimensionFourDependence
