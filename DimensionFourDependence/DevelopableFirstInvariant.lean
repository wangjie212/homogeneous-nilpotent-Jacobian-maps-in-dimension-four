import DimensionFourDependence.DevelopableRadialExclusion
import DimensionFourDependence.FiberInvariantDataForWitness
import DimensionFourDependence.HomogeneousFiberWeights

/-! # The actual developable graph has nonzero first fiber invariant

The actual source-normal pairing is its nonzero graph-normal coordinate
times the actual first invariant in every independent output chart.
Section 4.1 therefore makes that invariant nonzero for a nonplanar
developable image. All actual coefficients and the rank-one Hessian
are supplied in the chart of any constructed fiber-equation witness.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

section Pairing

variable {F : Type*} [Field F]

/-- The original-coordinate normal pairing factors through the
normalized graph pairing in any simultaneous coordinate chart. -/
theorem graph_normal_radial_pairing_identity
    (ν x : Fin 4 → F) (p : Equiv.Perm (Fin 4)) (z : Fin 3 → F)
    (hlast : ν (p 3) ≠ 0) (hcoord : ∀ i, ν (p i.castSucc) / ν (p 3) = -z i) :
    (∑ j, ν j * x j) = ν (p 3) * (x (p 3) - ∑ i : Fin 3, z i * x (p i.castSucc)) := by
  have hv (i : Fin 3) : ν (p i.castSucc) = -z i * ν (p 3) := (div_eq_iff hlast).mp (hcoord i)
  have hs : (∑ i : Fin 3, ν (p i.castSucc) * x (p i.castSucc)) =
      -(ν (p 3) * ∑ i : Fin 3, z i * x (p i.castSucc)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hv i]
    ring
  calc
    _ = (∑ i : Fin 3, ν (p i.castSucc) * x (p i.castSucc)) + ν (p 3) * x (p 3) := by
      rw [← Equiv.sum_comp p (fun j => ν j * x j), Fin.sum_univ_castSucc]
      rfl
    _ = _ := by rw [hs]; ring

end Pairing

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- The actual source-normal pairing equals the actual graph-normal
pivot times the actual first fiber invariant in the original chart. -/
theorem ImageRelationWitness.radial_pairing_eq_first_invariant
    (H : Fin 4 → MvPolynomial (Fin 4) K) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K) _ (H (p 3)))
    (I : ImageRelationWitness H) :
    (∑ i, rationalImageNormal H I.equation i * rationalCoordinate (K := K) i) =
      rationalImageNormal H I.equation (p 3) * firstFiberInvariantInChart p
        (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
          (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))) hY h := by
  obtain ⟨hlast, hcoord⟩ := I.gauss_chart_ratios H p hY h hh
  exact graph_normal_radial_pairing_identity (rationalImageNormal H I.equation)
    (rationalCoordinate (K := K)) p _ hlast hcoord

/-- The first invariant is nonzero for every actual independent graph
chart of a nonplanar homogeneous developable image. -/
theorem ImageRelationWitness.developable_first_invariant_ne_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I ≤ 1) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K) _ (H (p 3))) :
    firstFiberInvariantInChart p (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))) hY h ≠ 0 := by
  intro hz
  apply independent_developable_image_radial_pairing_ne_zero H hd hH hind I hGauss
  rw [I.radial_pairing_eq_first_invariant H p hY h hh, hz, mul_zero]

/-- The actual one-dimensional Gauss-image condition is exactly rank
one of the actual coefficient Hessian in every independent output chart. -/
theorem ImageRelationWitness.gauss_dimension_one_iff_hessian_rank_one
    (H : Fin 4 → MvPolynomial (Fin 4) K) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K) _ (H (p 3)))
    (I : ImageRelationWitness H) : gaussImageDimension H I = 1 ↔
      (coefficientHessian (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))) hY h).rank = 1 := by
  rw [I.gauss_image_dimension_eq_hessian H p hY h hh]
  norm_cast

/-- Any actual fiber-equation witness of the original nonplanar
homogeneous nilpotent rank-three developable map supplies all four
actual invariant coefficients, nonzero first invariant, its actual
Euler weight, and the actual rank-one coefficient Hessian. -/
theorem developable_fiber_witness_nonzero_weighted_invariants
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I ≤ 1)
    (W : FiberEquationWitness (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i))) :
    ∃ h c q k : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))),
      (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K) _ (H (W.chart 3)) ∧
      (c : FractionRing (MvPolynomial (Fin 4) K)) = firstFiberInvariantInChart W.chart
        (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
          (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))) W.independent h ∧
      (q : FractionRing (MvPolynomial (Fin 4) K)) = secondFiberInvariant W.chart
        (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
          (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))) W.independent h c ∧
      (k : FractionRing (MvPolynomial (Fin 4) K)) = thirdFiberInvariant W.chart
        (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
          (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))) W.independent h c q ∧
      c ≠ 0 ∧
      coefficientEuler _ W.independent h = h ∧
      coefficientEuler _ W.independent c = algebraMap K _ ((d : K)⁻¹) * c ∧
      (coefficientHessian (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))) W.independent h).rank = 1 := by
  obtain ⟨h, c, q, k, hh, hc, hq, hk⟩ := fiberEquationWitness_exists_invariant_coefficients H hN hrank W
  have hc0 : c ≠ 0 := by
    intro hz
    apply I.developable_first_invariant_ne_zero H hd hH hind hGauss W.chart W.independent h hh
    rw [← hc, hz]
    rfl
  have hg1 : gaussImageDimension H I = 1 := (Cardinal.le_one_iff.mp hGauss).resolve_left
    (fun hz => hind (componentsDependent_of_gauss_image_dimension_zero H hd hH I hz))
  have hess := (I.gauss_dimension_one_iff_hessian_rank_one H W.chart W.independent h hh).mp hg1
  exact ⟨h, c, q, k, hh, hc, hq, hk, hc0,
    homogeneous_last_output_euler H hd hH W.chart W.independent h hh,
    firstFiberInvariant_output_weight H hd hH W.chart W.independent h c hh hc, hess⟩

end DimensionFourDependence
