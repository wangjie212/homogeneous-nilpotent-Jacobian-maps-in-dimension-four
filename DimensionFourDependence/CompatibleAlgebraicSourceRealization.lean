import DimensionFourDependence.AlgebraicSourceTensorRealization
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Algebraic parameter coefficients retain one compatible source realization

A compatible closed-field image in algebraically closed geometric
constants extends to every algebraic coefficient field. The same
extension and the original source embedding then realize the entire
source tensor fraction field, retaining both factors exactly.
-/

namespace DimensionFourDependence

open scoped TensorProduct

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K C S L E G : Type*} [Field K] [CharZero K] [Field C] [Field S]
    [Field L] [Field E] [Field G]
    [Algebra K C] [Algebra K S] [Algebra C S] [IsScalarTower K C S]
    [Algebra C L] [Algebra.IsAlgebraic C L] [IsDomain (S ⊗[C] L)]
    [Algebra K E] [Algebra K G] [Algebra E G] [IsScalarTower K E G] [IsAlgClosed E]

/-- Extending the actual closed coefficient realization to algebraic
coefficients constructs one fraction-field realization preserving the
original source, every extended coefficient and the original base action. -/
theorem compatible_closed_field_realization_extends_to_algebraic_source_fraction_field
    (hclosed : algebraicClosure C S = ⊥) (f : S →ₐ[K] G) (g : C →ₐ[K] E)
    (hg : ∀ c : C, algebraMap E G (g c) = f (algebraMap C S c)) :
    ∃ σ : L →+* E, (∀ c : C, σ (algebraMap C L c) = g c) ∧
      ∃ φ : FractionRing (S ⊗[C] L) →+* G,
        (∀ s : S, φ (algebraMap (S ⊗[C] L) (FractionRing (S ⊗[C] L)) (s ⊗ₜ[C] (1 : L))) = f s) ∧
        (∀ l : L, φ (algebraMap (S ⊗[C] L) (FractionRing (S ⊗[C] L)) ((1 : S) ⊗ₜ[C] l)) =
          algebraMap E G (σ l)) := by
  classical
  let : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  let : Algebra C E := g.toRingHom.toAlgebra
  let : Algebra C G := ((algebraMap E G).comp g.toRingHom).toAlgebra
  let : IsScalarTower C E G := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let σ : L →ₐ[C] E := IsAlgClosed.lift
  let fC : S →ₐ[C] G :=
    { f.toRingHom with
      commutes' c := by
        change f (algebraMap C S c) = algebraMap E G (g c)
        exact (hg c).symm }
  let σG : L →ₐ[C] G := (IsScalarTower.toAlgHom C E G).comp σ
  obtain ⟨φ, hsource, hcoeff⟩ :=
    relatively_closed_algebraic_source_tensor_constructs_fraction_realization hclosed fC σG
  exact ⟨σ.toRingHom, σ.commutes, φ.toRingHom, hsource, hcoeff⟩

end DimensionFourDependence
