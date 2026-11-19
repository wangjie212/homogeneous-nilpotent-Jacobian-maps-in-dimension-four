import DimensionFourDependence.NormalizedRulingAlgebraicity
import DimensionFourDependence.ActualBoundaryNonGeneric

/-! # Actual boundary coordinates are algebraic over the original Gauss field

A normalized nonalgebraic point on the actual ruling would have the
generic output's homogeneous relations, hence would be the original
image generic point. The checked boundary exclusion rules this out.
This obtains the finite-branch algebraicity directly in the actual
boundary residue field, without assuming a closed incidence image.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)

/-- The actual original Gauss field as a specified subfield of the
actual boundary coefficient extension, preserving its source realization. -/
noncomputable def actualBoundaryOriginalGaussField
    (I : ImageRelationWitness H) (κ : Type u) [Field κ] [Algebra (L) κ] [Algebra K κ]
    [IsScalarTower K (L) κ] : IntermediateField K κ :=
  ((IsScalarTower.toAlgHom K (L) κ).comp (actualChartGaussFieldHom H hrank p hY I)).fieldRange

include hY

/-- A normalized point of the actual original ruling which is not
the image generic point has every coordinate algebraic over the actual
original Gauss field in its ambient coefficient extension. -/
theorem nongeneric_normalized_original_ruling_point_isAlgebraic
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hH0 : H ≠ 0)
    (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 1)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (hA : Module.finrank
      (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
      (LinearMap.ker (actualGaussRulingMatrix H I e).toLin') = 2)
    (κ : Type u) [Field κ] [Algebra (L) κ] [Algebra K κ] [IsScalarTower K (L) κ]
    (b : Fin 4 → κ) (hb0 : b ≠ 0) (a : Fin 4) (ha : b a = 1)
    (hb : (actualGaussRulingMatrix H I e).map
      ((algebraMap (L) κ).comp (actualChartGaussFieldHom H hrank p hY I).toRingHom) *ᵥ b = 0)
    (hng : projectiveFieldPoint (E := K) b hb0 ≠ projectiveImageGenericPoint H hd hH hH0) :
    ∀ i, IsAlgebraic (actualBoundaryOriginalGaussField H hrank p hY I κ) (b i) := by
  let M := projectiveRatioField (K := K)
    (rationalImageNormal H I.equation) (imageNormalPivot H I)
  let f : M →ₐ[K] κ :=
    (IsScalarTower.toAlgHom K (L) κ).comp (actualChartGaussFieldHom H hrank p hY I)
  let : Algebra M κ := f.toRingHom.toAlgebra
  let : IsScalarTower K M κ := IsScalarTower.of_algebraMap_eq (fun c => (f.commutes c).symm)
  have halg : ∀ i, IsAlgebraic M (b i) := by
    by_contra hn
    apply hng
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.ext'
    intro m R hR
    change R.IsHomogeneous m at hR
    rw [projectiveFieldPoint_homogeneous_mem b hb0 R hR]
    change aeval b R = 0 ↔ aeval H R = 0
    have he := normalized_kernel_non_algebraic_generic_homogeneous_relations
      (actualGaussRulingMatrix H I e) hA
      (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))
      (I.output_mem_actual_gauss_ruling H hd hH e)
      (actual_gauss_fiber_output_trdeg_two H hrank I hGauss) b hb a ha hn
      (MvPolynomial.map (algebraMap K M) R) (hR.map (algebraMap K M))
    rw [aeval_map_algebra_extension, aeval_map_algebra_extension, ← aeval_polynomial_to_fraction] at he
    exact he.trans (map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin 4) K) S₀))
  let J := f.fieldRange
  let : Algebra M J := f.equivFieldRange.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower M J κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  intro i
  exact (halg i).tower_top J

/-- Actual normalized full-fiber boundary coordinates are algebraic
over the original Gauss field. Ruling membership, nongenericity,
primitive factorization and the Gauss parameter are derived internally. -/
theorem actual_full_fiber_boundary_coordinates_algebraic_over_original_gauss
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 1)
    (h c q : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (κ : Type u) [Field κ] [Algebra (L) κ] [Algebra K κ] [IsScalarTower K (L) κ]
    (z : Option (Fin 4) → κ) (hz : z ≠ 0) (hb : (fun i => z (some i)) ≠ 0)
    (hboundary : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (rationalCoordinate (K := K) (n := 4)))
    (hz0 : z none = 0) (a : Fin 4) (ha : z (some a) = 1) :
    ∀ i, IsAlgebraic (actualBoundaryOriginalGaussField H hrank p hY I κ) (z (some i)) := by
  obtain ⟨e, hA, _⟩ := actual_gauss_fiber_ruling_polynomial_density H hd hH hrank hind I hGauss
  obtain ⟨g, P, _r, _hr, hg, _hgh, hP, hprim, hHP, hPdeg⟩ :=
    exists_primitive_factorization_common_degree_le_sub_two H hH hind I
  have hruling := actual_full_fiber_boundary_mem_original_gauss_ruling H hrank p hY I e h hh
    hd hH hGauss c q hc hq κ z hz hboundary hz0
  have hng := actual_full_fiber_boundary_on_original_ruling_not_generic H hrank p hY
    hd hH (rank_three_polynomial_map_ne_zero H hrank) hN hind I hGauss e hA
    g hg P (by omega) hP hprim hHP κ z hz hb hboundary hruling
  exact nongeneric_normalized_original_ruling_point_isAlgebraic H hrank p hY hd hH
    (rank_three_polynomial_map_ne_zero H hrank) I hGauss e hA κ (fun i => z (some i)) hb a ha hruling hng

end DimensionFourDependence
