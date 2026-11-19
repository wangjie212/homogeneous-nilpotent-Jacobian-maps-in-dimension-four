import DimensionFourDependence.FiniteRelativeNormalization
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # The integral reduced closure of a scheme point

This constructs the closed scheme, its actual closed immersion, and its
reduced and integral structures. It will be applied to the generic point
of the original projective pencil, rather than leaving its projective
scheme or chart gluing as an unspecified input.
-/

namespace DimensionFourDependence

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

universe u

variable (X : Scheme.{u}) (x : X)

/-- The vanishing ideal sheaf of the closure of the given point. -/
noncomputable def reducedPointClosureIdeal : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩

/-- The actual reduced closed scheme carried by the point closure. -/
noncomputable def reducedPointClosureScheme : Scheme.{u} :=
  (reducedPointClosureIdeal X x).subscheme

/-- Its canonical closed inclusion into the original scheme. -/
noncomputable def reducedPointClosureInclusion : reducedPointClosureScheme X x ⟶ X :=
  (reducedPointClosureIdeal X x).subschemeι

/-- The closed immersion has precisely the point closure as its image. -/
theorem reducedPointClosureInclusion_range :
    Set.range (reducedPointClosureInclusion X x) = closure {x} := by
  change Set.range (reducedPointClosureIdeal X x).subschemeι = closure {x}
  exact (Scheme.IdealSheafData.range_subschemeι _).trans (by
    simp only [reducedPointClosureIdeal,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_mk])

/-- This is a closed subscheme of the original scheme. -/
theorem reducedPointClosureInclusion_isClosedImmersion :
    IsClosedImmersion (reducedPointClosureInclusion X x) := by
  unfold reducedPointClosureInclusion
  infer_instance

/-- The reduced point closure is irreducible with the actual induced topology. -/
theorem reducedPointClosureScheme_irreducibleSpace :
    IrreducibleSpace (reducedPointClosureScheme X x) := by
  apply Subtype.irreducibleSpace
  simpa only [reducedPointClosureIdeal,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_mk] using
    (isIrreducible_singleton (x := x)).closure

/-- The affine quotient charts of the vanishing ideal sheaf are reduced,
so the glued closed scheme is reduced. -/
theorem reducedPointClosureScheme_isReduced : IsReduced (reducedPointClosureScheme X x) := by
  let I := reducedPointClosureIdeal X x
  have hquot (U : X.affineOpens) : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) := by
    apply (Ideal.isRadical_iff_quotient_reduced _).mp
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  let : ∀ U : X.affineOpens, IsReduced (I.subschemeCover.openCover.X U) := fun U => by
    let : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) := hquot U
    exact inferInstanceAs (IsReduced (Spec (CommRingCat.of (Γ(X, U) ⧸ I.ideal U))))
  exact @IsReduced.of_openCover I.subscheme I.subschemeCover.openCover this

/-- A point's reduced closure is an integral scheme, without a separate
integrality or gluing hypothesis. -/
theorem reducedPointClosureScheme_isIntegral : IsIntegral (reducedPointClosureScheme X x) := by
  let : IrreducibleSpace (reducedPointClosureScheme X x) :=
    reducedPointClosureScheme_irreducibleSpace X x
  let : IsReduced (reducedPointClosureScheme X x) := reducedPointClosureScheme_isReduced X x
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end DimensionFourDependence
