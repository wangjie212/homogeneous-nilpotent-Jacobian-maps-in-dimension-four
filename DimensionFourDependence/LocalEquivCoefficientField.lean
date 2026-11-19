import DimensionFourDependence.Defs
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Coefficients and parameter residues descend through local isomorphisms

The inverse of a source local algebra isomorphism transports an upstairs
coefficient field into the original source ring. The transported map
retains the original coefficients, its target realization, and its source
function-field realization. A rational curve parameter then has
transcendental residue without a separate horizontal-residue assumption.
-/

namespace DimensionFourDependence

variable {K C A B : Type*} [Field K] [Field C] [CommRing A] [CommRing B]
  [Algebra A B] [Algebra K A] [Algebra K B] [Algebra K C] [Algebra C B]
  [IsScalarTower K A B] [IsScalarTower K C B]

/-- The coefficient field descends to the original local source ring
through the actual inverse source algebra isomorphism. -/
noncomputable def localEquivCoefficientAlgHom (u : A ≃ₐ[A] B) : C →ₐ[K] A :=
  (u.symm.restrictScalars K).toAlgHom.comp (IsScalarTower.toAlgHom K C B)

/-- Full target-compatibility statement, kept opaque to instance search
when its rings are concrete projective chart localizations. -/
def CoefficientTargetCompatible (f : C →ₐ[K] A) : Prop :=
  ∀ c : C, algebraMap A B (f c) = algebraMap C B c

/-- Full rational-parameter residue statement for a coefficient embedding. -/
def CoefficientParameterResidueTranscendental [IsLocalRing A]
    (f : C →ₐ[K] A) (e : RatFunc K ≃ₐ[K] C) : Prop :=
  Transcendental K (IsLocalRing.residue A (f (e RatFunc.X)))

/-- Every coefficient-field embedding in a local ring has transcendental
rational-parameter residue. The residue map is injective on a field. -/
theorem coefficientAlgHom_parameter_residue_transcendental [IsLocalRing A]
    (f : C →ₐ[K] A) (e : RatFunc K ≃ₐ[K] C) :
    CoefficientParameterResidueTranscendental f e := by
  let j : C →ₐ[K] IsLocalRing.ResidueField A :=
    (IsScalarTower.toAlgHom K A (IsLocalRing.ResidueField A)).comp f
  intro ha
  change IsAlgebraic K (j (e RatFunc.X)) at ha
  have hc : IsAlgebraic K (e RatFunc.X) := (isAlgebraic_algHom_iff j j.injective).mp ha
  exact RatFunc.transcendental_X ((isAlgebraic_algHom_iff e.toAlgHom e.injective).mp hc)

/-- The descended coefficient is the same upstairs coefficient under
the original local source map. -/
theorem localEquivCoefficientAlgHom_target (u : A ≃ₐ[A] B) (c : C) :
    algebraMap A B (localEquivCoefficientAlgHom (K := K) u c) = algebraMap C B c := by
  have hu (a : A) : u a = algebraMap A B a := by simpa using u.commutes a
  rw [← hu]
  exact u.apply_symm_apply (algebraMap C B c)

/-- All coefficient values are preserved under the local source map. -/
theorem localEquivCoefficientAlgHom_target_compatible (u : A ≃ₐ[A] B) :
    CoefficientTargetCompatible (B := B)
      (localEquivCoefficientAlgHom (K := K) (C := C) (A := A) (B := B) u) :=
  localEquivCoefficientAlgHom_target (K := K) (C := C) (A := A) (B := B) u

/-- The coefficient embedding together with its full target realization.
Packaging the proof prevents concrete chart proofs from normalizing the
inverse local equivalence a second time. -/
noncomputable def localEquivCoefficientLift (u : A ≃ₐ[A] B) :
    {f : C →ₐ[K] A // CoefficientTargetCompatible (B := B) f} :=
  ⟨localEquivCoefficientAlgHom (K := K) (C := C) (A := A) (B := B) u,
    localEquivCoefficientAlgHom_target_compatible (K := K) (C := C) (A := A) (B := B) u⟩

variable {F : Type*} [CommRing F] [Algebra A F] [Algebra B F] [Algebra C F]
  [IsScalarTower A B F] [IsScalarTower C B F]

/-- Descent also preserves a compatible actual function-field inclusion. -/
theorem localEquivCoefficientAlgHom_source (u : A ≃ₐ[A] B) (c : C) :
    algebraMap A F (localEquivCoefficientAlgHom (K := K) u c) = algebraMap C F c := by
  rw [IsScalarTower.algebraMap_apply A B F, localEquivCoefficientAlgHom_target,
    ← IsScalarTower.algebraMap_apply C B F]

omit [Algebra A F] [Algebra B F] [Algebra C F] [IsScalarTower A B F] [IsScalarTower C B F] in
/-- A rational curve parameter has transcendental residue after actual
coefficient descent through the local source isomorphism. -/
theorem localEquivCoefficientAlgHom_parameter_residue_transcendental [IsLocalRing A]
    (u : A ≃ₐ[A] B) (e : RatFunc K ≃ₐ[K] C) :
    Transcendental K (IsLocalRing.residue A (localEquivCoefficientAlgHom (K := K) u (e RatFunc.X))) := by
  let j : C →ₐ[K] IsLocalRing.ResidueField A :=
    (IsScalarTower.toAlgHom K A (IsLocalRing.ResidueField A)).comp (localEquivCoefficientAlgHom (K := K) u)
  intro ha
  change IsAlgebraic K (j (e RatFunc.X)) at ha
  have hc : IsAlgebraic K (e RatFunc.X) := (isAlgebraic_algHom_iff j j.injective).mp ha
  exact RatFunc.transcendental_X ((isAlgebraic_algHom_iff e.toAlgHom e.injective).mp hc)

end DimensionFourDependence
