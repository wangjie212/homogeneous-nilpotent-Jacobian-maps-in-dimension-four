import DimensionFourDependence.MonicHypersurfaceProjection
import DimensionFourDependence.MonicProjectionSectionBound

/-! # The hypersurface-degree bound from actual normalized chart sections

Affine projection coordinates and the original equation construct the
monic finite projection. Actual normalized finite and infinity chart
coefficients, with the hyperplane transition, then bound an arbitrary
section's order in the given normal local ring by the original degree.
-/

namespace DimensionFourDependence

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {F k B L σ : Type u} [Field F] [Field k] [CharZero k] [Algebra F k]
  [CommRing B] [IsLocalRing B] [IsIntegrallyClosed B] [Field L]
  [Algebra F L] [Algebra (RatFunc k) L] [Algebra (Polynomial k) L]
  [IsScalarTower F (Polynomial k) L]
  [IsScalarTower (Polynomial k) (RatFunc k) L]
  [Algebra (Polynomial k) B] [Algebra B L] [IsFractionRing B L]
  [IsScalarTower (Polynomial k) B L]
  [Algebra (rationalInfinityRing k) L]
  [IsScalarTower (rationalInfinityRing k) (RatFunc k) L]

/-- A nonzero section represented by regular coefficients on the actual
normalized projection charts has local order at most the original
hypersurface total degree. Monicity, coefficient-degree bounds, finite
field degree, both section integrality conditions and the local
normalization-prime comparison are all derived. -/
theorem hypersurface_projection_regular_section_order_le_totalDegree
    (s : σ → Polynomial k) (hs : ∀ i, (s i).natDegree ≤ 1)
    (f : MvPolynomial (Option σ) F) (hf : f ≠ 0)
    (hfull : f.degreeOf none = f.totalDegree)
    (v : L) (hgen : IntermediateField.adjoin (RatFunc k) {v} = ⊤)
    (hroot : MvPolynomial.aeval
      (fun i => i.elim v (fun j => algebraMap (Polynomial k) L (s j))) f = 0)
    (sectionValue : MonicProjectionSection (k := k) v)
    (p : Polynomial k) (hp : Irreducible p)
    (hpB : algebraMap (Polynomial k) B p ∈ IsLocalRing.maximalIdeal B)
    (b : B) (hb : b ≠ 0)
    (hvalue : (sectionValue.finiteValue : L) = algebraMap B L b)
    (a : ℕ) (horder : b ∈ (IsLocalRing.maximalIdeal B) ^ a) :
    a ≤ f.totalDegree := by
  obtain ⟨P, hP, hPdegree, hPcoeff, hProot⟩ :=
    exists_monic_hypersurface_projection_equation s hs f hf hfull v hroot
  exact (monic_projection_regular_section_order_le_degree
    P hP hPcoeff v hgen hProot sectionValue p hp hpB b hb hvalue a horder).trans_eq hPdegree

end DimensionFourDependence
