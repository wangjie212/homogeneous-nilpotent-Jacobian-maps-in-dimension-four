import DimensionFourDependence.MonicProjectionSection
import DimensionFourDependence.NormalLocalSectionBound
import DimensionFourDependence.SimpleFieldDegreeBound

/-! # Multiplicity for regular sections of a monic normalized projection

The original monic equation constructs a finite projection of bounded
degree. Actual normalized chart regularity and the hyperplane transition
then give the arbitrary section bound in its given normal local ring.
No integrality condition on the section or degree bound is assumed.
-/

namespace DimensionFourDependence

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k L : Type u} [Field k] [Field L]
  [Algebra (RatFunc k) L] [Algebra (Polynomial k) L]
  [IsScalarTower (Polynomial k) (RatFunc k) L]

/-- A monic projection equation for the actual field generator
constructs finiteness and bounds the actual extension degree. -/
theorem monic_projection_finite_and_degree_le
    (P : Polynomial (Polynomial k)) (hP : P.Monic)
    (v : L) (hgen : IntermediateField.adjoin (RatFunc k) {v} = ⊤)
    (hroot : Polynomial.aeval v P = 0) :
    Module.Finite (RatFunc k) L ∧ Module.finrank (RatFunc k) L ≤ P.natDegree := by
  let A := algebraMap (Polynomial k) (RatFunc k)
  have hroot' : Polynomial.aeval v (P.map A) = 0 := by
    change Polynomial.eval₂ (algebraMap (RatFunc k) L) v (P.map A) = 0
    rw [Polynomial.eval₂_map]
    change Polynomial.eval₂
      ((algebraMap (RatFunc k) L).comp (algebraMap (Polynomial k) (RatFunc k))) v P = 0
    rw [← IsScalarTower.algebraMap_eq (Polynomial k) (RatFunc k) L]
    exact hroot
  obtain ⟨hfinite, hdegree⟩ := generating_root_finite_and_degree_le
    v hgen (P.map A) (hP.map A).ne_zero hroot'
  exact ⟨hfinite, hdegree.trans_eq (hP.natDegree_map A)⟩

variable [CharZero k] {B : Type u} [CommRing B] [IsLocalRing B] [IsIntegrallyClosed B]
  [Algebra (Polynomial k) B] [Algebra B L] [IsFractionRing B L]
  [IsScalarTower (Polynomial k) B L]
  [Algebra (rationalInfinityRing k) L]
  [IsScalarTower (rationalInfinityRing k) (RatFunc k) L]

/-- Every nonzero section regular on the actual normalized finite and
infinity charts, with their hyperplane-frame transition, has local order
at most the original monic projection degree. This bounds its actual value
in the given normal local ring, with all auxiliary integrality, finiteness
and normalization-prime comparison data constructed. -/
theorem monic_projection_regular_section_order_le_degree
    (P : Polynomial (Polynomial k)) (hP : P.Monic)
    (hdegree : ∀ i ≤ P.natDegree, (P.coeff i).natDegree + i ≤ P.natDegree)
    (v : L) (hgen : IntermediateField.adjoin (RatFunc k) {v} = ⊤)
    (hroot : Polynomial.aeval v P = 0)
    (s : MonicProjectionSection (k := k) v)
    (p : Polynomial k) (hp : Irreducible p)
    (hpB : algebraMap (Polynomial k) B p ∈ IsLocalRing.maximalIdeal B)
    (b : B) (hb : b ≠ 0) (hvalue : (s.finiteValue : L) = algebraMap B L b)
    (a : ℕ) (horder : b ∈ (IsLocalRing.maximalIdeal B) ^ a) :
    a ≤ P.natDegree := by
  obtain ⟨hfinite, hfieldDegree⟩ := monic_projection_finite_and_degree_le P hP v hgen hroot
  let : Module.Finite (RatFunc k) L := hfinite
  have hs := monic_projection_regular_section_two_integralities P hP hdegree v hroot s
  have hbfinite : IsIntegral (Polynomial k) (algebraMap B L b) :=
    Eq.mp (congrArg (fun z : L => IsIntegral (Polynomial k) z) hvalue) hs.1
  have hbinfinity : IsIntegral (rationalInfinityRing k)
      (algebraMap (RatFunc k) L (RatFunc.X⁻¹) * algebraMap B L b) :=
    Eq.mp (congrArg (fun z : L => IsIntegral (rationalInfinityRing k)
      (algebraMap (RatFunc k) L (RatFunc.X⁻¹) * z)) hvalue) hs.2
  exact (normal_local_section_order_le_projection_degree
    p hp hpB b hb hbfinite hbinfinity a horder).trans hfieldDegree

end DimensionFourDependence
