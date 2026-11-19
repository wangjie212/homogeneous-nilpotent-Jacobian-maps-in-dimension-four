import DimensionFourDependence.ActualFullBoundaryOriginalRuling
import DimensionFourDependence.ActualBoundaryRulingExclusion

/-! # The actual full generic-fiber boundary excludes the image generic point

The actual invariant equations derive ruling membership. Ruling density
derives the original Gauss-parameter comparison. Actual closure equations
and Lemma 4.3 exclude a generic original image direction. Finally the
original map constructs the chart, invariants, primitive factorization
and rational Gauss parameter needed for this conclusion.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]

/-- In any actual invariant chart, an actual full-fiber boundary
direction at infinity cannot be the original projective image generic
point. Ruling membership and parameter comparison are derived. -/
theorem actual_full_fiber_boundary_not_generic_from_invariants
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hH0 : H ≠ 0)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 1)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h c q : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) = firstFiberInvariantInChart p
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))) hY h)
    (hq : (q : FractionRing (MvPolynomial (Fin 4) K)) = secondFiberInvariant p
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))) hY h c)
    (g : MvPolynomial (Fin 4) K) (hg : g ≠ 0) (P : Fin 4 → MvPolynomial (Fin 4) K)
    {D : ℕ} (hD : 0 < D) (hP : IsHomogMap P D) (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (κ : Type u) [Field κ]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) κ]
    [Algebra K κ]
    [IsScalarTower K (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) κ]
    (z : Option (Fin 4) → κ) (hz : z ≠ 0) (hb : (fun i => z (some i)) ≠ 0)
    (hboundary : projectiveFieldPoint
      (E := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) z hz ∈
      projectiveClosureSet
        (L := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
          (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) (rationalCoordinate (K := K) (n := 4)))
    (hz0 : z none = 0) :
    projectiveFieldPoint (E := K) (fun i => z (some i)) hb ≠ projectiveImageGenericPoint H hd hH hH0 := by
  obtain ⟨e, hA, _⟩ := actual_gauss_fiber_ruling_polynomial_density H hd hH hrank hind I hGauss
  have hruling := actual_full_fiber_boundary_mem_original_gauss_ruling H hrank p hY I e h hh
    hd hH hGauss c q hc hq κ z hz hboundary hz0
  exact actual_full_fiber_boundary_on_original_ruling_not_generic H hrank p hY hd hH hH0 hN hind I hGauss
    e hA g hg P hD hP hprim hHP κ z hz hb hboundary hruling

/-- The original nonplanar homogeneous nilpotent rank-three map of
Gauss dimension one constructs an actual output chart in which every
actual full-fiber boundary direction at infinity is nongeneric on the
original image. All parameter, invariant and primitive data are derived. -/
theorem original_map_constructs_full_boundary_generic_point_exclusion
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 1) :
    ∃ (p : Equiv.Perm (Fin 4))
      (_hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))),
      let L := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))
      ∀ (κ : Type u) [Field κ] [Algebra L κ] [Algebra K κ] [IsScalarTower K L κ]
        (z : Option (Fin 4) → κ) (hz : z ≠ 0) (hb : (fun i => z (some i)) ≠ 0),
        projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet (L := L) (rationalCoordinate (K := K) (n := 4)) →
        z none = 0 →
        projectiveFieldPoint (E := K) (fun i => z (some i)) hb ≠
          projectiveImageGenericPoint H hd hH (rank_three_polynomial_map_ne_zero H hrank) := by
  obtain ⟨W⟩ := exists_fiber_equation_witness_polynomial H hN hrank
  obtain ⟨h, c, q, _k, hh, hc, hq, _hk⟩ := fiberEquationWitness_exists_invariant_coefficients H hN hrank W
  obtain ⟨g, P, _a, _ha, hg, _hgh, hP, hprim, hHP, hPdegree⟩ :=
    exists_primitive_factorization_common_degree_le_sub_two H hH hind I
  refine ⟨W.chart, W.independent, ?_⟩
  dsimp only
  intro κ _ _ _ _ z hz hb hboundary hz0
  exact actual_full_fiber_boundary_not_generic_from_invariants H hd hH (rank_three_polynomial_map_ne_zero H hrank)
    hN hrank hind I hGauss W.chart W.independent h c q hh hc hq g hg P (by omega) hP hprim hHP
    κ z hz hb hboundary hz0

end DimensionFourDependence
