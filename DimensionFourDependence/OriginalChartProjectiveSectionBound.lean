import DimensionFourDependence.ProjectiveSectionProjectionRegularity
import DimensionFourDependence.ProjectionGeneratorOriginalField
import DimensionFourDependence.NormalLocalSectionBound
import DimensionFourDependence.MonicProjectionSectionBound
import DimensionFourDependence.MonicHypersurfaceProjection

/-! # Arbitrary original-chart global sections satisfy the hypersurface bound

The section is regular on the actual normalizations of the four original
projective charts. The original coordinate field, actual linear projection
values and monic degree-bounded equation construct the field generator,
finite field degree and both section integrality conditions. The norm
argument then bounds the given section value in its actual normal local
ring, without assuming those auxiliary properties.
-/

namespace DimensionFourDependence

universe u

open MvPolynomial Matrix

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {F k B L : Type u} [Field F] [Field k] [CharZero k] [Field L]
  [Algebra F k] [Algebra F L] [Algebra (RatFunc k) L] [IsScalarTower F (RatFunc k) L]
  [Algebra (Polynomial k) L] [IsScalarTower (Polynomial k) (RatFunc k) L]
  [Algebra (rationalInfinityRing k) L]
  [IsScalarTower (rationalInfinityRing k) (RatFunc k) L]
  [CommRing B] [IsLocalRing B] [IsIntegrallyClosed B]
  [Algebra (Polynomial k) B] [Algebra B L] [IsFractionRing B L]
  [IsScalarTower (Polynomial k) B L]

/-- A nonzero global section represented in the original normalized
projective frames has local order bounded by the actual monic projection
degree. The original chart coordinates generate the field; the single
fiber generator, finiteness, field-degree bound, both section integrality
conditions and the local normalization-prime comparison are derived. -/
theorem original_chart_projective_section_order_le_projection_degree
    (x : Fin 4 → L) (sectionValue : ProjectiveNormalizedSection (k := F) x)
    (s : Fin 4 ≃ Option (Fin 3)) (hbase : x (s.symm none) ≠ 0)
    (hfield : IntermediateField.adjoin F
      (Set.range (fun j => x (s.symm (some j)) / x (s.symm none))) = ⊤)
    (T : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) (v : L) (u : k)
    (hcoordinates : linearProjectionCoordinate T
      (fun j => x (s.symm (some j)) / x (s.symm none)) =
      ![v, algebraMap (RatFunc k) L RatFunc.X, algebraMap (RatFunc k) L (RatFunc.C u)])
    (P : Polynomial (Polynomial k)) (hP : P.Monic)
    (hdegree : ∀ i ≤ P.natDegree, (P.coeff i).natDegree + i ≤ P.natDegree)
    (hroot : Polynomial.aeval v P = 0)
    (p : Polynomial k) (hp : Irreducible p)
    (hpB : algebraMap (Polynomial k) B p ∈ IsLocalRing.maximalIdeal B)
    (b : B) (hb : b ≠ 0)
    (hvalue : (sectionValue.coefficient (s.symm none) : L) = algebraMap B L b)
    (a : ℕ) (horder : b ∈ (IsLocalRing.maximalIdeal B) ^ a) : a ≤ P.natDegree := by
  have hgen := projection_fiber_generator_of_original_coordinates
    T _ hfield v ![RatFunc.X, RatFunc.C u] hcoordinates
  obtain ⟨hfinite, hfieldDegree⟩ := monic_projection_finite_and_degree_le P hP v hgen hroot
  let : Module.Finite (RatFunc k) L := hfinite
  obtain ⟨hfiniteSection, hinfinitySection⟩ := projective_original_chart_section_two_projection_regularities
    x sectionValue s hbase T v u hcoordinates P hP hdegree hroot
  have hfiniteValue : IsIntegral (Polynomial k) (algebraMap B L b) :=
    Eq.mp (congrArg (fun z : L => IsIntegral (Polynomial k) z) hvalue) hfiniteSection
  have hinfinityValue : IsIntegral (rationalInfinityRing k)
      (algebraMap (RatFunc k) L (RatFunc.X⁻¹) * algebraMap B L b) :=
    Eq.mp (congrArg (fun z : L => IsIntegral (rationalInfinityRing k)
      (algebraMap (RatFunc k) L (RatFunc.X⁻¹) * z)) hvalue) hinfinitySection
  exact (normal_local_section_order_le_projection_degree
    p hp hpB b hb hfiniteValue hinfinityValue a horder).trans hfieldDegree

variable [IsScalarTower F (Polynomial k) L]

/-- The original full-fiber-degree hypersurface equation and original
normalized chart section coefficients give the original total-degree
bound. The monic projection equation and all coefficient-degree bounds
are constructed from this actual equation, rather than supplied. -/
theorem original_chart_projective_section_order_le_hypersurface_degree
    (x : Fin 4 → L) (sectionValue : ProjectiveNormalizedSection (k := F) x)
    (s : Fin 4 ≃ Option (Fin 3)) (hbase : x (s.symm none) ≠ 0)
    (hfield : IntermediateField.adjoin F
      (Set.range (fun j => x (s.symm (some j)) / x (s.symm none))) = ⊤)
    (T : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) (v : L) (u : k)
    (hcoordinates : linearProjectionCoordinate T
      (fun j => x (s.symm (some j)) / x (s.symm none)) =
      ![v, algebraMap (RatFunc k) L RatFunc.X, algebraMap (RatFunc k) L (RatFunc.C u)])
    (g : MvPolynomial (Option (Fin 2)) F) (hg : g ≠ 0)
    (hfull : g.degreeOf none = g.totalDegree)
    (hrelation : MvPolynomial.aeval (fun i : Option (Fin 2) => i.elim v
      (fun j => ![algebraMap (RatFunc k) L RatFunc.X,
        algebraMap (RatFunc k) L (RatFunc.C u)] j)) g = 0)
    (p : Polynomial k) (hp : Irreducible p)
    (hpB : algebraMap (Polynomial k) B p ∈ IsLocalRing.maximalIdeal B)
    (b : B) (hb : b ≠ 0)
    (hvalue : (sectionValue.coefficient (s.symm none) : L) = algebraMap B L b)
    (a : ℕ) (horder : b ∈ (IsLocalRing.maximalIdeal B) ^ a) : a ≤ g.totalDegree := by
  let z : Fin 2 → Polynomial k := ![Polynomial.X, Polynomial.C u]
  have hz : ∀ j, (z j).natDegree ≤ 1 := by intro j; fin_cases j <;> simp [z]
  have hroot : MvPolynomial.aeval (fun i : Option (Fin 2) => i.elim v
      (fun j => algebraMap (Polynomial k) L (z j))) g = 0 := by
    have hcoords : (fun j => algebraMap (Polynomial k) L (z j)) =
        ![algebraMap (RatFunc k) L RatFunc.X, algebraMap (RatFunc k) L (RatFunc.C u)] := by
      funext j
      fin_cases j
      · change algebraMap (Polynomial k) L Polynomial.X = _
        rw [IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) L, RatFunc.algebraMap_X]
        rfl
      · change algebraMap (Polynomial k) L (Polynomial.C u) = _
        rw [IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) L, RatFunc.algebraMap_C]
        rfl
    rw [hcoords]
    exact hrelation
  obtain ⟨P, hP, hPdegree, hPcoeff, hProot⟩ :=
    exists_monic_hypersurface_projection_equation z hz g hg hfull v hroot
  exact (original_chart_projective_section_order_le_projection_degree
    x sectionValue s hbase hfield T v u hcoordinates P hP hPcoeff hProot
    p hp hpB b hb hvalue a horder).trans_eq hPdegree

end DimensionFourDependence
