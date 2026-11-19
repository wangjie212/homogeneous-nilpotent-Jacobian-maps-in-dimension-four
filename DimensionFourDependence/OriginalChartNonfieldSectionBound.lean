import DimensionFourDependence.OriginalChartProjectiveSectionBound
import DimensionFourDependence.FiniteProjectionLocalCenter

/-! # The original-chart section bound without a supplied base polynomial

The original monic projection constructs the finite function-field
extension. A nonfield local center then supplies its irreducible base
polynomial, so neither the polynomial nor its membership in the maximal
ideal is an additional geometric hypothesis.
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
  [CommRing B] [IsDomain B] [IsLocalRing B] [IsIntegrallyClosed B]
  [Algebra (Polynomial k) B] [Algebra B L] [IsFractionRing B L]
  [IsScalarTower (Polynomial k) B L]

/-- A nonfield normal local ring and the actual monic projection give
the section bound, with the local base polynomial constructed internally. -/
theorem original_chart_nonfield_section_order_le_projection_degree
    (hmax : IsLocalRing.maximalIdeal B ≠ ⊥)
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
    (b : B) (hb : b ≠ 0)
    (hvalue : (sectionValue.coefficient (s.symm none) : L) = algebraMap B L b)
    (a : ℕ) (horder : b ∈ (IsLocalRing.maximalIdeal B) ^ a) : a ≤ P.natDegree := by
  have hgen := projection_fiber_generator_of_original_coordinates
    T _ hfield v ![RatFunc.X, RatFunc.C u] hcoordinates
  have hfinite := (monic_projection_finite_and_degree_le P hP v hgen hroot).1
  let : Module.Finite (RatFunc k) L := hfinite
  obtain ⟨p, hp, hpB⟩ := finite_rational_projection_exists_irreducible_center
    (k := k) (L := L) hmax
  exact original_chart_projective_section_order_le_projection_degree
    x sectionValue s hbase hfield T v u hcoordinates P hP hdegree hroot
    p hp hpB b hb hvalue a horder

variable [IsScalarTower F (Polynomial k) L]

/-- The original full-fiber-degree hypersurface gives the degree bound
at every nonfield normal local center, without a supplied base polynomial. -/
theorem original_chart_nonfield_section_order_le_hypersurface_degree
    (hmax : IsLocalRing.maximalIdeal B ≠ ⊥)
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
  exact (original_chart_nonfield_section_order_le_projection_degree
    hmax x sectionValue s hbase hfield T v u hcoordinates P hP hPcoeff hProot
    b hb hvalue a horder).trans_eq hPdegree

end DimensionFourDependence
