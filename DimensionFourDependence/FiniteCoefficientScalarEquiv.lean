import DimensionFourDependence.ActualGaussBoundaryRootConstruction

/-! # Finite coefficient fields retain their specified original scalar field

A finite extension of an actual parameter image is also finite over
the original parameter field through their specified field isomorphism.
Its ambient embedding agrees with that scalar action whenever the
original parameter realization does. These are the coefficient actions
required by the native pencil construction.
-/

namespace DimensionFourDependence

variable {C J E : Type*} [Field C] [Field J] [Field E] [Algebra J E]

/-- The original parameter field acts on a finite extension of its
specified image through the actual parameter-field isomorphism. -/
@[instance_reducible]
noncomputable def finiteCoefficientScalarAlgebra (e : C ≃+* J) : Algebra C E :=
  ((algebraMap J E).comp e.toRingHom).toAlgebra

/-- Finiteness over the actual parameter image implies finiteness
over its specified original parameter field, with the exact scalar action. -/
theorem finiteCoefficientScalarAlgebra_finite (e : C ≃+* J) [Module.Finite J E] :
    letI : Algebra C E := finiteCoefficientScalarAlgebra (E := E) e
    Module.Finite C E := by
  let : Algebra C J := e.toRingHom.toAlgebra
  let : Algebra C E := finiteCoefficientScalarAlgebra (E := E) e
  let : IsScalarTower C J E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Module.Finite C J := Module.Finite.of_surjective (Algebra.linearMap C J) e.surjective
  exact Module.Finite.trans (R := C) J E

/-- The transferred finite coefficient extension is algebraic over
the original parameter field with that same specified scalar action. -/
theorem finiteCoefficientScalarAlgebra_isAlgebraic (e : C ≃+* J) [Module.Finite J E] :
    letI : Algebra C E := finiteCoefficientScalarAlgebra (E := E) e
    Algebra.IsAlgebraic C E := by
  let : Algebra C E := finiteCoefficientScalarAlgebra (E := E) e
  let : Module.Finite C E := finiteCoefficientScalarAlgebra_finite (E := E) e
  infer_instance

variable {κ : Type*} [Field κ] [Algebra J κ] [Algebra E κ] [IsScalarTower J E κ] [Algebra C κ]

/-- The transferred scalar action agrees with the actual ambient
coefficient embedding when the original parameter realization does. -/
theorem finiteCoefficientScalarAlgebra_target_tower (e : C ≃+* J)
    (hcompat : ∀ c : C, algebraMap C κ c = algebraMap J κ (e c)) :
    letI : Algebra C E := finiteCoefficientScalarAlgebra (E := E) e
    IsScalarTower C E κ := by
  let : Algebra C E := finiteCoefficientScalarAlgebra (E := E) e
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change algebraMap C κ c = algebraMap E κ (algebraMap J E (e c))
  rw [hcompat, ← IsScalarTower.algebraMap_apply J E κ]

end DimensionFourDependence
