import DimensionFourDependence.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Prime-local residues and quotient fraction fields agree over their original constants -/

namespace DimensionFourDependence

set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000

variable {E R : Type*} [CommRing E] [CommRing R] [Algebra E R]

/-- The residue field of the actual prime localization is the
fraction field of the same original prime quotient, over the same
original coefficient ring. -/
noncomputable def primeLocalizationResidueFractionAlgEquiv (Q : Ideal R) [Q.IsPrime] :
    IsLocalRing.ResidueField (Localization.AtPrime Q) ≃ₐ[E] FractionRing (R ⧸ Q) :=
  ((FractionRing.algEquiv (R ⧸ Q) Q.ResidueField).symm).restrictScalars E

/-- The explicit residue/fraction identification retains the value
of every original regular source element. -/
theorem primeLocalizationResidueFractionAlgEquiv_source (Q : Ideal R) [Q.IsPrime] (r : R) :
    primeLocalizationResidueFractionAlgEquiv (E := E) Q
      (IsLocalRing.residue (Localization.AtPrime Q) (algebraMap R (Localization.AtPrime Q) r)) =
      algebraMap R (FractionRing (R ⧸ Q)) r := by
  let e := (FractionRing.algEquiv (R ⧸ Q) Q.ResidueField).symm
  have he := e.commutes (Ideal.Quotient.mk Q r)
  change e (algebraMap R Q.ResidueField r) = algebraMap R (FractionRing (R ⧸ Q)) r
  rw [IsScalarTower.algebraMap_apply R (R ⧸ Q) Q.ResidueField,
    IsScalarTower.algebraMap_apply R (R ⧸ Q) (FractionRing (R ⧸ Q))]
  exact he


/-- A scalar-compatible actual local-ring identification followed by
the prime-residue fraction-field identification. -/
noncomputable def localPrimeResidueFractionAlgEquiv
    {A : Type*} [CommRing A] [IsLocalRing A] [Algebra E A]
    (Q : Ideal R) [Q.IsPrime] (β : A ≃ₐ[E] Localization.AtPrime Q) :
    IsLocalRing.ResidueField A ≃ₐ[E] FractionRing (R ⧸ Q) :=
  (IsLocalRing.ResidueField.mapAlgEquiv (R := E) β).trans
    (primeLocalizationResidueFractionAlgEquiv (E := E) Q)

/-- The combined local comparison preserves every specified
original regular value before specialization. -/
theorem localPrimeResidueFractionAlgEquiv_source
    {A : Type*} [CommRing A] [IsLocalRing A] [Algebra E A]
    (Q : Ideal R) [Q.IsPrime] (β : A ≃ₐ[E] Localization.AtPrime Q)
    (x : A) (r : R) (hβ : β x = algebraMap R (Localization.AtPrime Q) r) :
    localPrimeResidueFractionAlgEquiv (E := E) Q β (IsLocalRing.residue A x) =
      algebraMap R (FractionRing (R ⧸ Q)) r := by
  let δ := primeLocalizationResidueFractionAlgEquiv (E := E) Q
  calc
    _ = δ (IsLocalRing.ResidueField.mapAlgEquiv (R := E) β (IsLocalRing.residue A x)) := rfl
    _ = δ (IsLocalRing.residue (Localization.AtPrime Q) (β x)) :=
      congrArg δ (IsLocalRing.ResidueField.mapAlgEquiv_residue (R := E) β x)
    _ = δ (IsLocalRing.residue (Localization.AtPrime Q) (algebraMap R (Localization.AtPrime Q) r)) :=
      congrArg (fun y => δ (IsLocalRing.residue (Localization.AtPrime Q) y)) hβ
    _ = algebraMap R (FractionRing (R ⧸ Q)) r :=
      primeLocalizationResidueFractionAlgEquiv_source (E := E) Q r

end DimensionFourDependence
