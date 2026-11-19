import DimensionFourDependence.AlgebraicConstantsFinite
import Mathlib.FieldTheory.FinTrdeg

/-! # Algebraic subextensions of a finitely generated field are finite

A finite transcendence basis gives an actual rational-coordinate field.
The ambient finitely generated field is algebraic, hence finite, over
that rational field. The algebraic-constants rank comparison then makes
every algebraic subextension finite, including the actual relative closure.
-/

namespace DimensionFourDependence

universe u

variable {K E : Type u} [Field K] [Field E] [Algebra K E]
  [Algebra.EssFiniteType K E] {n : ℕ}

/-- A finite transcendence basis of a finitely generated field gives
a finite extension of its actual abstract rational-coordinate field. -/
theorem finite_rational_extension_of_transcendence_basis
    (Y : Fin n → E) (hY : IsTranscendenceBasis K Y) :
    letI : Algebra (FractionRing (MvPolynomial (Fin n) K)) E :=
      (rationalOutputHom Y hY.1).toRingHom.toAlgebra
    Module.Finite (FractionRing (MvPolynomial (Fin n) K)) E := by
  let B := FractionRing (MvPolynomial (Fin n) K)
  let I := IntermediateField.adjoin K (Set.range Y)
  let g : B →ₐ[K] E := rationalOutputHom Y hY.1
  let e : B ≃ₐ[K] I := rationalOutputEquiv Y hY.1
  let : Algebra B E := g.toRingHom.toAlgebra
  let : IsScalarTower K B E :=
    IsScalarTower.of_algebraMap_eq (fun k => (g.commutes k).symm)
  let : Algebra I B := e.symm.toRingHom.toAlgebra
  let : IsScalarTower I B E := IsScalarTower.of_algebraMap_eq (by
    intro a
    change (a : E) = g (e.symm a)
    change (a : E) = ((e (e.symm a) : I) : E)
    rw [e.apply_symm_apply])
  let : Algebra.IsAlgebraic I E := hY.isAlgebraic_field
  let : Algebra.IsAlgebraic B E := ⟨fun x =>
    (Algebra.IsAlgebraic.isAlgebraic (R := I) x).tower_top B⟩
  let : Algebra.EssFiniteType B E := Algebra.EssFiniteType.of_comp K B E
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

variable {C : Type u} [Field C] [Algebra K C] [Algebra C E] [IsScalarTower K C E]
  [Algebra.IsAlgebraic K C]

include E in
/-- Every algebraic subextension of an essentially finite-type field
extension is finite over the original field. -/
theorem algebraic_subextension_finite_of_essFiniteType : Module.Finite K C := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis K E
  let e : Fin s.card ≃ s := s.equivFin.symm
  let Y : Fin s.card → E := fun i => (e i : E)
  have hY : IsTranscendenceBasis K Y := hs.comp_equiv e
  exact algebraic_constants_finite_of_finite_rational_extension Y hY.1
    (finite_rational_extension_of_transcendence_basis Y hY)

end DimensionFourDependence
