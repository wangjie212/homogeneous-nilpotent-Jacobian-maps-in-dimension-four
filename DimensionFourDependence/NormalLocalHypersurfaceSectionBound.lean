import DimensionFourDependence.NormalLocalSectionBound
import DimensionFourDependence.ProjectionDefiningPolynomial
import DimensionFourDependence.ProjectionFieldGenerator

/-! # The original hypersurface degree bounds arbitrary local section orders

The two independent projection coordinates, three original field
generators and their original hypersurface equation construct both the
finite projection and its degree bound. The section is arbitrary and its
local-ring value is the one whose order is bounded.
-/

namespace DimensionFourDependence

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {F k B L : Type u} [Field F] [Field k] [CharZero k]
  [CommRing B] [IsLocalRing B] [IsIntegrallyClosed B]
  [Field L] [Algebra (RatFunc k) L]
  [Algebra F (RatFunc k)] [Algebra F L] [IsScalarTower F (RatFunc k) L]
  [Algebra (Polynomial k) B] [Algebra (Polynomial k) L]
  [Algebra B L] [IsFractionRing B L]
  [IsScalarTower (Polynomial k) (RatFunc k) L]
  [IsScalarTower (Polynomial k) B L]
  [Algebra (rationalInfinityRing k) L]
  [IsScalarTower (rationalInfinityRing k) (RatFunc k) L]

/-- Independent projection coordinates and the actual three-generator
hypersurface equation construct finiteness and the degree bound; the
given arbitrary section's finite and infinity regularity then bound its
order in the given normal local ring by that original total degree. -/
theorem normal_local_section_order_le_hypersurface_totalDegree
    (u w : RatFunc k) (hs : AlgebraicIndependent F
      (fun i : Option Unit => i.elim w (fun _ => u)))
    (v : L) (hgen : IntermediateField.adjoin F
      {algebraMap (RatFunc k) L u, algebraMap (RatFunc k) L w, v} = ⊤)
    (f : MvPolynomial (Option (Option Unit)) F) (hf : f ≠ 0)
    (hroot : MvPolynomial.aeval
      (fun i => i.elim v (fun j => algebraMap (RatFunc k) L
        (j.elim w (fun _ => u)))) f = 0)
    (p : Polynomial k) (hp : Irreducible p)
    (hpB : algebraMap (Polynomial k) B p ∈ IsLocalRing.maximalIdeal B)
    (b : B) (hb : b ≠ 0)
    (hfinite : IsIntegral (Polynomial k) (algebraMap B L b))
    (hinfinity : IsIntegral (rationalInfinityRing k)
      (algebraMap (RatFunc k) L (RatFunc.X⁻¹) * algebraMap B L b))
    (a : ℕ) (horder : b ∈ (IsLocalRing.maximalIdeal B) ^ a) :
    a ≤ f.totalDegree := by
  have hgenerate : IntermediateField.adjoin (RatFunc k) {v} = ⊤ :=
    projection_field_generator_of_three_coordinates _ _ v hgen ⟨u, rfl⟩ ⟨w, rfl⟩
  obtain ⟨hfiniteField, hdegree⟩ := projection_hypersurface_field_degree_le
    (fun i : Option Unit => i.elim w (fun _ => u)) hs v hgenerate f hf hroot
  let : Module.Finite (RatFunc k) L := hfiniteField
  exact (normal_local_section_order_le_projection_degree
    p hp hpB b hb hfinite hinfinity a horder).trans hdegree

end DimensionFourDependence
