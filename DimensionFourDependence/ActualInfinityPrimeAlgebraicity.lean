import DimensionFourDependence.ProjectivePrimeBaseExtension
import DimensionFourDependence.ActualBoundaryGaussAlgebraicity

/-! # Every actual extended infinity prime has an algebraic normalized coordinate field

Represent every relevant homogeneous prime of the extended original
infinity section by its actual normalized coordinate field. The original
ruling-preservation boundary argument applies to this representative.
Its Gauss-field algebraicity implies algebraicity over the extended
coefficient field, and the coordinates generate the whole normalized
field. Thus extended partial derivatives apply to every such prime,
without an assumed closed-point or residue-field classification.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

section Image

variable {K F R : Type*} [Field K] [Field F] [Field R]
    [Algebra K F] [Algebra K R] [Algebra F R] [IsScalarTower K F R]

/-- Algebraicity over an actual subfield of the coefficient image
implies algebraicity over the original coefficient field itself. -/
theorem isAlgebraic_of_subfield_le_coefficient_image
    (J : IntermediateField K R)
    (hJ : J ≤ (IsScalarTower.toAlgHom K F R).fieldRange) (x : R) (hx : IsAlgebraic J x) :
    IsAlgebraic F x := by
  let g := IsScalarTower.toAlgHom K F R
  let rho : J →+* F := g.equivFieldRange.symm.toRingHom.comp (IntermediateField.inclusion hJ).toRingHom
  have hcomp : (algebraMap F R).comp rho = algebraMap J R := by
    apply RingHom.ext
    intro a
    exact congrArg (fun b : g.fieldRange => (b : R))
      (g.equivFieldRange.apply_symm_apply (IntermediateField.inclusion hJ a))
  obtain ⟨P, hP, hPx⟩ := hx
  refine ⟨P.map rho, ?_, ?_⟩
  · simpa only [Polynomial.map_zero] using (Polynomial.map_injective rho rho.injective).ne hP
  · change Polynomial.eval₂ (algebraMap F R) x (P.map rho) = 0
    rw [Polynomial.eval₂_map, hcomp]
    exact hPx

end Image

universe u

attribute [local instance] coefficientFieldScalarTower

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
local notation "x" => rationalCoordinate (K := K) (n := 4)

variable (F : Type u) [Field F]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) F]
    [Algebra K F]
    [IsScalarTower K (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) F]

include hrank

/-- All normalized coordinates of every prime of the actual original
infinity section after the specified coefficient extension are algebraic
over that coefficient field. No field-valued-point coverage is assumed. -/
theorem actual_full_infinity_prime_normalized_coordinates_isAlgebraic
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 1)
    (h c q : L) (hh : (h : S₀) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p 3)))
    (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (z : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) F))
    (hext : Ideal.map (MvPolynomial.map (algebraMap (L) F)) (projectiveConeIdeal («L» := L) (x)) ≤
      z.asHomogeneousIdeal.toIdeal)
    (hinfinity : X none ∈ z.asHomogeneousIdeal)
    (a : Fin 4) (ha : X (some a) ∉ z.asHomogeneousIdeal) :
    ∀ i : Option (Fin 4), IsAlgebraic F (projectivePrimeRatioCoordinate z (some a) i) := by
  let R := projectivePrimeRatioField z (some a)
  let b := projectivePrimeRatioCoordinate z (some a)
  let : IsScalarTower K (L) R := IsScalarTower.of_algebraMap_eq (fun k => by
    rw [IsScalarTower.algebraMap_apply K F R, IsScalarTower.algebraMap_apply (L) F R,
      ← IsScalarTower.algebraMap_apply K (L) F])
  have hb0 : b ≠ 0 := projectivePrimeRatioCoordinate_ne_zero z (some a) ha
  have hnorm : b (some a) = 1 := projectivePrimeRatioCoordinate_self z (some a) ha
  have hzero : b none = 0 := projectivePrimeRatioCoordinate_zero_of_mem z (some a) none hinfinity
  have hb : (fun i : Fin 4 => b (some i)) ≠ 0 := by
    intro hzero'
    have he := congrFun hzero' a
    rw [hnorm] at he
    exact one_ne_zero he
  have hboundary := normalized_extended_projective_prime_mem_original_closure (x) z hext (some a) ha
  have halg := actual_full_fiber_boundary_coordinates_algebraic_over_original_gauss H hrank p hY
    hd hH hN hind I hGauss h c q hh hc hq R b hb0 hb hboundary hzero a hnorm
  have hJ : actualBoundaryOriginalGaussField H hrank p hY I R ≤
      (IsScalarTower.toAlgHom K F R).fieldRange := by
    rintro v ⟨m, rfl⟩
    refine ⟨algebraMap (L) F (actualChartGaussFieldHom H hrank p hY I m), ?_⟩
    change algebraMap F R (algebraMap (L) F (actualChartGaussFieldHom H hrank p hY I m)) =
      algebraMap (L) R (actualChartGaussFieldHom H hrank p hY I m)
    exact (IsScalarTower.algebraMap_apply (L) F R _).symm
  intro i
  cases i with
  | none =>
    change IsAlgebraic F (b none)
    rw [hzero]
    exact isAlgebraic_zero
  | some i =>
    exact isAlgebraic_of_subfield_le_coefficient_image
      (actualBoundaryOriginalGaussField H hrank p hY I R) hJ (b (some i)) (halg i)

/-- The entire actual normalized coordinate field of every extended
infinity prime is algebraic over the extended coefficient field. -/
theorem actual_full_infinity_prime_normalized_field_isAlgebraic
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 1)
    (h c q : L) (hh : (h : S₀) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p 3)))
    (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (z : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) F))
    (hext : Ideal.map (MvPolynomial.map (algebraMap (L) F)) (projectiveConeIdeal («L» := L) (x)) ≤
      z.asHomogeneousIdeal.toIdeal)
    (hinfinity : X none ∈ z.asHomogeneousIdeal)
    (a : Fin 4) (ha : X (some a) ∉ z.asHomogeneousIdeal) :
    Algebra.IsAlgebraic F (projectivePrimeRatioField z (some a)) :=
  projectivePrimeRatioField_isAlgebraic_of_coordinates z (some a)
    (actual_full_infinity_prime_normalized_coordinates_isAlgebraic H hrank p hY F
      hd hH hN hind I hGauss h c q hh hc hq z hext hinfinity a ha)

end DimensionFourDependence
