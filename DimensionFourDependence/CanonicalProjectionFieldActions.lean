import DimensionFourDependence.NormalizationPrimeFunctionField
import DimensionFourDependence.ResidueProjectionActionCompatibility
import DimensionFourDependence.CanonicalProjectionResidueParameter

/-! # Projection field actions at the actual canonical normalization prime

The actual two base coordinates of a finite surface projection supply an
independent pair in the original affine function field. A height-one prime
selects a transcendental residue coordinate, and hence constructs the
entire compatible iterated rational projection action at that prime.
-/

namespace DimensionFourDependence

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {k A : Type u} [Field k] [CommRing A] [IsDomain A] [Algebra k A]

/-- The fully constructed iterated rational, regular polynomial and
infinity actions at the actual normalization prime, including their
original values and all constant-field compatibilities. -/
def canonicalProjectionFieldActions
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] (z : Fin 2 → A) : Prop :=
    let : Algebra (Localization.AtPrime Q) (FractionRing A) := normalizationPrimeFractionAlgebra Q
    let : IsScalarTower k (Localization.AtPrime Q) (FractionRing A) :=
      normalizationPrimeFractionAlgebra_base_scalarTower Q
    ∃ j : Fin 2,
    ∃ hu : Transcendental k (IsLocalRing.residue (Localization.AtPrime Q)
      (algebraMap A (Localization.AtPrime Q) (z j))),
    ∃ hp : AlgebraicIndependent k
      ![algebraMap (Localization.AtPrime Q) (FractionRing A)
          (algebraMap A (Localization.AtPrime Q) (z j)),
        algebraMap (Localization.AtPrime Q) (FractionRing A)
          (algebraMap A (Localization.AtPrime Q) (z (Equiv.swap (0 : Fin 2) j 1)))],
      residueProjectionActionsCompatible
        (algebraMap A (Localization.AtPrime Q) (z j))
        (algebraMap A (Localization.AtPrime Q) (z (Equiv.swap (0 : Fin 2) j 1))) hu hp

/-- Independent original projection coordinates and an actual
transcendental residue construct every projection action at the given
canonical normalization prime, with all original values preserved. -/
theorem canonical_normalization_independent_projection_actions
    (z : Fin 2 → A) (hind : AlgebraicIndependent k z)
    (Q : Ideal (normalizationRing A)) [Q.IsPrime]
    (hres : ∃ j : Fin 2, Transcendental k
      (IsLocalRing.residue (Localization.AtPrime Q)
        (algebraMap A (Localization.AtPrime Q) (z j)))) :
    canonicalProjectionFieldActions (k := k) Q z := by
  classical
  let B := Localization.AtPrime Q
  let L := FractionRing A
  let : Algebra B L := normalizationPrimeFractionAlgebra Q
  let : IsScalarTower A B L := normalizationPrimeFractionAlgebra_source_scalarTower Q
  let : IsScalarTower k B L := normalizationPrimeFractionAlgebra_base_scalarTower Q
  have hfield : AlgebraicIndependent k (fun i => algebraMap A L (z i)) :=
    hind.map' (f := IsScalarTower.toAlgHom k A L) (IsFractionRing.injective A L)
  obtain ⟨j, hu⟩ := hres
  have hp : AlgebraicIndependent k
      ![algebraMap B L (algebraMap A B (z j)),
        algebraMap B L (algebraMap A B (z (Equiv.swap (0 : Fin 2) j 1)))] := by
    simp only [← IsScalarTower.algebraMap_apply A B L]
    exact algebraicIndependent_pair_selected_first _ hfield j
  exact ⟨j, hu, hp, residue_projection_actions_compatible _ _ hu hp⟩

variable [CharZero k] [Algebra.FiniteType k A]

/-- Every divisor of the actual canonical normalization of a finite
surface projection constructs its iterated rational projection field and
the compatible regular polynomial and infinity actions internally. -/
theorem canonical_normalization_finite_projection_field_actions
    (y : Option (Fin 2) → A)
    (hfinite : Module.Finite (affineProjectionAlgebra (k := k) y) A)
    (htr : 2 ≤ Algebra.trdeg k A)
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] (hQ : Q.height = 1) :
    canonicalProjectionFieldActions (k := k) Q (fun j => y (some j)) := by
  exact canonical_normalization_independent_projection_actions
    (fun j => y (some j))
    (affine_finite_surface_projection_algebraicIndependent y htr hfinite) Q
    (canonical_normalization_finite_projection_transcendental_residue y hfinite htr Q hQ)

end DimensionFourDependence
