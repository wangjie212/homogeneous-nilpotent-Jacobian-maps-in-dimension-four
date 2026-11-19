import DimensionFourDependence.InfinityScaledMonicRoot
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # Regular framed sections on actual normalized projection charts

Both chart rings are subalgebras of the specified function field, and
their normalizations are actual integral closures in that same field.
Regular coefficients with the hyperplane-frame transition construct both
integrality conditions required by the norm argument.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {R L : Type*} [CommRing R] [Field L] [Algebra R L]

/-- A regular function on the actual normalization of an integral
one-generator chart is integral over the chart's original base ring. -/
theorem normalized_adjoin_regular_value_isIntegral
    (v : L) (hv : IsIntegral R v)
    (z : integralClosure (Algebra.adjoin R {v}) L) : IsIntegral R (z : L) := by
  let A := Algebra.adjoin R {v}
  let : Algebra.IsIntegral R A := (Subalgebra.isIntegral_iff A).mpr
    (fun x hx => adjoin_le_integralClosure hv hx)
  exact isIntegral_trans (R := R) (A := A) (z : L) z.property

variable {k : Type*} [Field k]
  [Algebra (RatFunc k) L] [Algebra (Polynomial k) L]
  [IsScalarTower (Polynomial k) (RatFunc k) L]
  [Algebra (rationalInfinityRing k) L]
  [IsScalarTower (rationalInfinityRing k) (RatFunc k) L]

/-- The original finite projection chart, inside the given function field. -/
noncomputable def monicProjectionFiniteChart (v : L) : Subalgebra (Polynomial k) L :=
  Algebra.adjoin (Polynomial k) {v}

/-- The projection chart over the actual local base at infinity. -/
noncomputable def monicProjectionInfinityChart (v : L) : Subalgebra (rationalInfinityRing k) L :=
  Algebra.adjoin (rationalInfinityRing k) {algebraMap (RatFunc k) L (RatFunc.X⁻¹) * v}

/-- Regular coefficients in the actual normalized finite and infinity
charts, with the transition for the pulled-back hyperplane bundle. -/
structure MonicProjectionSection (v : L) where
  finiteValue : integralClosure (monicProjectionFiniteChart (k := k) v) L
  infinityValue : integralClosure (monicProjectionInfinityChart (k := k) v) L
  transition : (infinityValue : L) =
    algebraMap (RatFunc k) L (RatFunc.X⁻¹) * (finiteValue : L)

/-- Regularity on both actual normalized charts constructs the finite
and infinity integrality hypotheses; neither is supplied as an assumption
about the section. The monic original equation supplies the chart data. -/
theorem monic_projection_regular_section_two_integralities
    (P : Polynomial (Polynomial k)) (hP : P.Monic)
    (hdegree : ∀ i ≤ P.natDegree, (P.coeff i).natDegree + i ≤ P.natDegree)
    (v : L) (hroot : Polynomial.aeval v P = 0)
    (s : MonicProjectionSection (k := k) v) :
    IsIntegral (Polynomial k) (s.finiteValue : L) ∧
      IsIntegral (rationalInfinityRing k)
        (algebraMap (RatFunc k) L (RatFunc.X⁻¹) * (s.finiteValue : L)) := by
  have hv : IsIntegral (Polynomial k) v := ⟨P, hP, hroot⟩
  have hvinfinity := infinity_scaled_root_isIntegral_of_monic_degree_bounds P hP hdegree v hroot
  refine ⟨normalized_adjoin_regular_value_isIntegral v hv s.finiteValue, ?_⟩
  have hs := normalized_adjoin_regular_value_isIntegral
    (algebraMap (RatFunc k) L (RatFunc.X⁻¹) * v) hvinfinity s.infinityValue
  exact Eq.mp (congrArg (fun z : L => IsIntegral (rationalInfinityRing k) z) s.transition) hs

end DimensionFourDependence
