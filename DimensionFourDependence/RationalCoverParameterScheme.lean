import DimensionFourDependence.NormalizedCurveEtaleOpen
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # An actual normalized affine parameter curve for a rational-field cover

The integral closure of K[t] in the specified finite extension field
supplies an actual affine scheme, its generic-field morphism, and the
original K-structure. Its fraction field is the specified extension.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K E : Type u) [Field K] [CharZero K] [Field E] [Algebra (RatFunc K) E]

noncomputable local instance (priority := 1) parameterPolynomialAlgebra : Algebra (Polynomial K) E :=
  ((algebraMap (RatFunc K) E).comp (algebraMap (Polynomial K) (RatFunc K))).toAlgebra

local instance parameterPolynomialTower : IsScalarTower (Polynomial K) (RatFunc K) E :=
  IsScalarTower.of_algebraMap_eq (R := Polynomial K) (S := RatFunc K) (A := E) (by intro r; rfl)

/-- The actual normalized affine parameter ring, with its specified
embedding in the finite extension field. -/
noncomputable def rationalCoverParameterRing : CommRingCat.{u} :=
  CommRingCat.of (integralClosure (Polynomial K) E)

/-- The original constant-field homomorphism into that normalized ring. -/
noncomputable def rationalCoverParameterBaseHom : CommRingCat.of K ⟶ rationalCoverParameterRing K E :=
  CommRingCat.ofHom ((algebraMap (Polynomial K) (integralClosure (Polynomial K) E)).comp Polynomial.C)

/-- The specified inclusion of the actual normalized parameter ring
in the original extension field. -/
noncomputable def rationalCoverParameterFieldHom : rationalCoverParameterRing K E ⟶ CommRingCat.of E :=
  CommRingCat.ofHom (integralClosure (Polynomial K) E).val

/-- This normalized curve retains the original constant-field action
inside the specified extension field. -/
theorem rationalCoverParameterBaseHom_field :
    rationalCoverParameterBaseHom K E ≫ rationalCoverParameterFieldHom K E =
      CommRingCat.ofHom ((algebraMap (RatFunc K) E).comp (algebraMap K (RatFunc K))) := by
  ext k
  change algebraMap (RatFunc K) E (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C k)) = _
  rw [show Polynomial.C k = algebraMap K (Polynomial K) k from rfl,
    ← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
  rfl

/-- The actual normalized affine parameter curve. -/
noncomputable def rationalCoverParameterScheme : Scheme.{u} :=
  Spec (rationalCoverParameterRing K E)

/-- The actual parameter ring is a domain inside the specified field. -/
theorem rationalCoverParameterRing_isDomain : IsDomain (rationalCoverParameterRing K E) := by
  exact inferInstanceAs (IsDomain (integralClosure (Polynomial K) E))

/-- The actual normalized affine parameter curve is integral. -/
theorem rationalCoverParameterScheme_isIntegral : IsIntegral (rationalCoverParameterScheme K E) := by
  let : IsDomain (rationalCoverParameterRing K E) := rationalCoverParameterRing_isDomain K E
  exact inferInstanceAs (IsIntegral (Spec (rationalCoverParameterRing K E)))

/-- Its structure map to the original constant field. -/
noncomputable def rationalCoverParameterSchemeToBase :
    rationalCoverParameterScheme K E ⟶ Spec (CommRingCat.of K) :=
  Spec.map (rationalCoverParameterBaseHom K E)

/-- The specified extension field gives an actual generic morphism
into the normalized affine parameter curve. -/
noncomputable def rationalCoverParameterGenericMorphism :
    Spec (CommRingCat.of E) ⟶ rationalCoverParameterScheme K E :=
  Spec.map (rationalCoverParameterFieldHom K E)

/-- The field morphism into the curve preserves the entire original
constant-field map. -/
theorem rationalCoverParameterGenericMorphism_over :
    rationalCoverParameterGenericMorphism K E ≫ rationalCoverParameterSchemeToBase K E =
      Spec.map (CommRingCat.ofHom ((algebraMap (RatFunc K) E).comp (algebraMap K (RatFunc K)))) := by
  unfold rationalCoverParameterGenericMorphism rationalCoverParameterSchemeToBase
  exact (Spec.map_comp (rationalCoverParameterBaseHom K E)
    (rationalCoverParameterFieldHom K E)).symm.trans
      (congrArg Spec.map (rationalCoverParameterBaseHom_field K E))

variable [Module.Finite (RatFunc K) E]

/-- The normalized parameter ring is finite over the actual original
polynomial parameter ring. -/
theorem rationalCoverParameterRing_finite :
    Module.Finite (Polynomial K) (integralClosure (Polynomial K) E) :=
  normalized_curve_cover_finite (R := Polynomial K) (k := RatFunc K) (L := E)

/-- The specified extension field really is the fraction field of
this actual normalized affine parameter ring. -/
theorem rationalCoverParameterRing_fractionField :
    letI : Algebra (rationalCoverParameterRing K E) E :=
      (rationalCoverParameterFieldHom K E).hom.toAlgebra
    IsFractionRing (rationalCoverParameterRing K E) E := by
  exact integralClosure.isFractionRing_of_finite_extension (RatFunc K) E

/-- This normalized parameter curve is Noetherian. -/
theorem rationalCoverParameterScheme_isNoetherian :
    IsNoetherian (rationalCoverParameterScheme K E) := by
  let : Module.Finite (Polynomial K) (integralClosure (Polynomial K) E) :=
    rationalCoverParameterRing_finite K E
  let : IsNoetherianRing (integralClosure (Polynomial K) E) :=
    Algebra.FiniteType.isNoetherianRing (Polynomial K) _
  exact inferInstanceAs (IsNoetherian (Spec (CommRingCat.of (integralClosure (Polynomial K) E))))

end DimensionFourDependence
