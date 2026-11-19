import DimensionFourDependence.ConstantGraphDirection
import DimensionFourDependence.GaussImageDimension
import DimensionFourDependence.HomogeneousCoefficientEuler

/-! # A fixed tangent vertex forces Gauss-image dimension at most one

The actual image normal, graph chart, Euler weight and coefficient Hessian
give the cone obstruction in Section 3.2. A fixed nonzero vector annihilating
the image normal is the explicit tangent-vertex hypothesis. Deriving it
from a concurrent covering family is a separate geometric step.
-/

namespace DimensionFourDependence

variable {F : Type*} [Field F]

/-- Divide a normal's fixed tangent-vector relation by its nonzero chart entry. -/
theorem normal_chart_constant_tangent_relation (ν C : Fin 4 → F)
    (p : Equiv.Perm (Fin 4)) (z : Fin 3 → F) (hlast : ν (p 3) ≠ 0)
    (hcoord : ∀ i, ν (p i.castSucc) / ν (p 3) = -z i)
    (htangent : ∑ j, C j * ν j = 0) :
    (∑ i, C (p i.castSucc) * z i) = C (p 3) := by
  have hdivide : (∑ j, C j * (ν j / ν (p 3))) = 0 := by
    simp only [← mul_div_assoc, ← Finset.sum_div, htangent, zero_div]
  have he : (∑ j, C (p j) * (ν (p j) / ν (p 3))) = 0 := by
    exact (Equiv.sum_comp p (fun j => C j * (ν j / ν (p 3)))).trans hdivide
  rw [Fin.sum_univ_castSucc] at he
  change (∑ i : Fin 3, C (p i.castSucc) * (ν (p i.castSucc) / ν (p 3))) +
    C (p 3) * (ν (p 3) / ν (p 3)) = 0 at he
  simp only [hcoord, div_self hlast, mul_one, mul_neg, Finset.sum_neg_distrib] at he
  linear_combination -he

variable {K : Type*} [Field K] [CharZero K]

omit [Field F] in
/-- A nonzero fixed vector tangent to the actual homogeneous image cone
forces its Gauss-image function field to have dimension at most one. -/
theorem ImageRelationWitness.gauss_dimension_le_one_of_constant_tangent_vertex
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K) _ (H (p 3)))
    (I : ImageRelationWitness H) (C : Fin 4 → K) (hC : C ≠ 0)
    (htangent : ∑ j, algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (C j) *
      rationalImageNormal H I.equation j = 0) :
    gaussImageDimension H I ≤ 1 := by
  let Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H (p i.castSucc))
  let : IsScalarTower K (coefficientField (K := K) Y)
    (FractionRing (MvPolynomial (Fin 4) K)) := coefficientFieldScalarTower Y
  obtain ⟨hlast, hcoord⟩ := I.gauss_chart_ratios H p hY h hh
  have hsource := normal_chart_constant_tangent_relation (rationalImageNormal H I.equation)
    (fun j => algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (C j))
    p (fiberGradient Y hY h) hlast hcoord htangent
  have hgradient : (∑ i, algebraMap K (coefficientField (K := K) Y) (C (p i.castSucc)) *
      coefficientGradient Y hY h i) = algebraMap K (coefficientField (K := K) Y) (C (p 3)) := by
    apply (algebraMap (coefficientField (K := K) Y) (FractionRing (MvPolynomial (Fin 4) K))).injective
    simpa only [map_sum, map_mul,
      ← IsScalarTower.algebraMap_apply K (coefficientField (K := K) Y)
        (FractionRing (MvPolynomial (Fin 4) K)), coefficientGradient,
      IntermediateField.algebraMap_apply, fiberGradient] using hsource
  have hfirst : (fun i : Fin 3 => C (p i.castSucc)) ≠ 0 := by
    intro hz
    have hb : C (p 3) = 0 := by
      apply (algebraMap K (coefficientField (K := K) Y)).injective
      rw [← hgradient]
      simp only [show ∀ i : Fin 3, C (p i.castSucc) = 0 from congrFun hz,
        map_zero, zero_mul, Finset.sum_const_zero]
    apply hC
    funext j
    obtain ⟨k, rfl⟩ := p.surjective j
    refine Fin.lastCases ?_ (fun i => ?_) k
    · change C (p 3) = 0
      exact hb
    · change C (p i.castSucc) = 0
      exact congrFun hz i
  have hrank := coefficientHessian_rank_le_one_of_constant_tangent Y hY h
    (homogeneous_last_output_euler H hd hH p hY h hh) _ hfirst (C (p 3)) hgradient
  rw [I.gauss_image_dimension_eq_hessian H p hY h hh]
  exact_mod_cast hrank

omit [Field F] in
/-- The polynomial image-normal version, with the graph chart constructed
from the original homogeneous nilpotent rank-three map. -/
theorem gauss_dimension_le_one_of_constant_image_normal_vertex
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (C : Fin 4 → K) (hC : C ≠ 0)
    (htangent : ∑ j, MvPolynomial.C (C j) * imageRelationNormal H I.equation j = 0) :
    gaussImageDimension H I ≤ 1 := by
  obtain ⟨p, hY, h, c, q, k, hh, _, _, _⟩ := exists_three_fiber_invariants_polynomial H hN hrank
  have hsource : ∑ j, algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (C j) *
      rationalImageNormal H I.equation j = 0 := by
    have he := congrArg (algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K))) htangent
    simp only [map_sum, map_mul, map_zero] at he
    change (∑ j, algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
      (algebraMap K (MvPolynomial (Fin 4) K) (C j)) * rationalImageNormal H I.equation j) = 0 at he
    simpa only [← IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K))] using he
  exact I.gauss_dimension_le_one_of_constant_tangent_vertex H hd hH p hY h hh C hC hsource

omit [Field F] in
/-- Gauss-image dimension two excludes every nonzero constant tangent vertex. -/
theorem gauss_dimension_two_no_constant_image_normal_vertex
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 2)
    (C : Fin 4 → K)
    (htangent : ∑ j, MvPolynomial.C (C j) * imageRelationNormal H I.equation j = 0) : C = 0 := by
  by_contra hC
  have hbound := gauss_dimension_le_one_of_constant_image_normal_vertex H hd hH hN hrank I C hC htangent
  rw [hGauss] at hbound
  norm_num at hbound

end DimensionFourDependence
