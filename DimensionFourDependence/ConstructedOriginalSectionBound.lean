import DimensionFourDependence.CanonicalFiniteProjectionSectionBound
import DimensionFourDependence.ConstructedAffineFiniteProjection

/-! # The section bound constructed from the original affine surface equation

The original generators and nonzero equation choose the finite linear
projection. Surface dimension and the actual divisor then construct its
independent residue parameter and all projection field actions. Every
nonzero original-chart normalized section is bounded by the original
equation degree, without auxiliary projection choices.
-/

namespace DimensionFourDependence

universe u

open MvPolynomial

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {k A : Type u} [Field k] [CharZero k]
  [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]

/-- The original nonzero surface equation bounds every original-chart
normalized section at each actual height-one normalization prime. The
finite projection, parameter, variable ordering, monic equation, field
degree, local base polynomial and section integrality are all constructed. -/
theorem canonical_original_section_order_le_original_equation_degree
    (c : Fin 3 → A) (hc : Algebra.adjoin k (Set.range c) = ⊤)
    (htr : 2 ≤ Algebra.trdeg k A)
    (f : MvPolynomial (Fin 3) k) (hf : f ≠ 0) (hroot : aeval c f = 0)
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] (hQ : Q.height = 1)
    (x : Fin 4 → FractionRing A) (sectionValue : ProjectiveNormalizedSection (k := k) x)
    (s : Fin 4 ≃ Option (Fin 3)) (hbase : x (s.symm none) ≠ 0)
    (hratios : (fun i => x (s.symm (some i)) / x (s.symm none)) =
      (fun i => algebraMap A (FractionRing A) (c i)))
    (b : Localization.AtPrime Q) (hb : b ≠ 0)
    (a : ℕ) (horder : b ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ a) :
    let : Algebra (Localization.AtPrime Q) (FractionRing A) := normalizationPrimeFractionAlgebra Q
    (sectionValue.coefficient (s.symm none) : FractionRing A) =
      algebraMap (Localization.AtPrime Q) (FractionRing A) b → a ≤ f.totalDegree := by
  obtain ⟨T, hgen, hg, hdegree, hfull, hroot', hfinite⟩ :=
    exists_actual_affine_finite_linear_projection c hc f hf hroot
  let : Algebra (Localization.AtPrime Q) (FractionRing A) := normalizationPrimeFractionAlgebra Q
  change (sectionValue.coefficient (s.symm none) : FractionRing A) =
    algebraMap (Localization.AtPrime Q) (FractionRing A) b → a ≤ f.totalDegree
  intro hvalue
  exact (canonical_finite_projection_original_section_order_le_degree
    c hc htr T _ hg hfull hroot' hfinite Q hQ x sectionValue s hbase hratios b hb a horder
    hvalue).trans_eq hdegree

end DimensionFourDependence
