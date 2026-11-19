import DimensionFourDependence.RectangularJacobianRank
import DimensionFourDependence.ImageEquationWitness

/-! # The actual image normal in the coefficient graph chart

The graph Jacobian and independent selected outputs force every
nonzero left normal to have a nonzero last chart entry. Its ratios are
the negative actual coefficient gradient, giving the affine Gauss chart.
-/

namespace DimensionFourDependence

open Matrix

variable {F : Type*} [Field F] {m n : ℕ}

/-- Independent matrix rows make the left vector action injective at zero. -/
theorem vecMul_zero_of_rows_independent
    (A : Matrix (Fin m) (Fin n) F) (hA : LinearIndependent F A.row)
    (v : Fin m → F) (hv : v ᵥ* A = 0) : v = 0 := by
  rw [Matrix.vecMul_eq_sum] at hv
  exact funext (Fintype.linearIndependent_iff.mp hA v hv)

variable {K : Type*} [Field K] [CharZero K]

omit [Field F] in
/-- A left normal of the actual graph satisfies the graph-gradient
relation in every selected coordinate. -/
theorem graph_left_normal_coordinate_relation
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
    (h : coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = H (p 3))
    (ν : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (hν : ν ᵥ* rationalJacobian H = 0) :
    ∀ i : Fin 3, ν (p i.castSucc) + ν (p 3) *
      fiberGradient (fun i : Fin 3 => H (p i.castSucc)) hY h i = 0 := by
  let Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K) := fun i => H (p i.castSucc)
  have he := chart_covector_jacobian H p hY h hh (ν ∘ p)
  have hcomp : (ν ∘ p) ∘ p.symm = ν := by
    funext j
    simp only [Function.comp_apply, p.apply_symm_apply]
  rw [hcomp, hν] at he
  have hz := vecMul_zero_of_rows_independent (rationalJacobian Y)
    (rationalJacobian_rows_independent Y hY) ((ν ∘ p) ᵥ* fiberFrame Y hY h) he.symm
  intro i
  have hi := congrFun hz i
  simpa [vecMul, dotProduct, Fin.sum_univ_castSucc, fiberFrame, Fin.snoc, Function.comp_apply] using hi

omit [Field F] in
/-- The last graph coordinate is a genuine nonzero chart coordinate
for every nonzero actual left normal. -/
theorem graph_left_normal_last_ne_zero
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
    (h : coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = H (p 3))
    (ν : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hν0 : ν ≠ 0) (hν : ν ᵥ* rationalJacobian H = 0) : ν (p 3) ≠ 0 := by
  intro hz
  apply hν0
  funext j
  obtain ⟨i, rfl⟩ := p.surjective j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · change ν (p 3) = 0
    exact hz
  · change ν (p i.castSucc) = 0
    simpa only [hz, zero_mul, add_zero] using graph_left_normal_coordinate_relation H p hY h hh ν hν i

omit [Field F] in
/-- The actual normal ratios are precisely the negative coefficient
gradient; the nonzero denominator is derived from the normal itself. -/
theorem graph_left_normal_ratios
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
    (h : coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = H (p 3))
    (ν : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hν0 : ν ≠ 0) (hν : ν ᵥ* rationalJacobian H = 0) (i : Fin 3) :
    ν (p i.castSucc) / ν (p 3) = -fiberGradient (fun i : Fin 3 => H (p i.castSucc)) hY h i := by
  apply (div_eq_iff (graph_left_normal_last_ne_zero H p hY h hh ν hν0 hν)).mpr
  linear_combination graph_left_normal_coordinate_relation H p hY h hh ν hν i

omit [Field F] [CharZero K] in
/-- The actual polynomial image normal viewed in the source function field. -/
noncomputable def rationalImageNormal
    (H : Fin 4 → MvPolynomial (Fin 4) K) (R : MvPolynomial (Fin 4) K) :
    Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
  fun i => algebraMap (MvPolynomial (Fin 4) K) _ (imageRelationNormal H R i)

omit [Field F] in
/-- The constructed image equation supplies the genuine Gauss chart
and its actual negative-gradient coordinates. -/
theorem ImageRelationWitness.gauss_chart_ratios
    (H : Fin 4 → MvPolynomial (Fin 4) K) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K) _ (H (p 3)))
    (I : ImageRelationWitness H) :
    rationalImageNormal H I.equation (p 3) ≠ 0 ∧ ∀ i : Fin 3,
      rationalImageNormal H I.equation (p i.castSucc) / rationalImageNormal H I.equation (p 3) =
        -fiberGradient (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
          (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))) hY h i := by
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) := fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  have hν0 : rationalImageNormal H I.equation ≠ 0 := by
    intro hz
    apply I.normal_ne_zero
    funext i
    apply IsFractionRing.injective (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
    simpa only [rationalImageNormal, map_zero, Pi.zero_apply] using congrFun hz i
  have hν : rationalImageNormal H I.equation ᵥ* rationalJacobian Q = 0 := by
    rw [rationalJacobian_polynomial H]
    exact imageRelationNormal_rational_left_kernel H I.equation I.vanishing
  exact ⟨graph_left_normal_last_ne_zero Q p hY h hh _ hν0 hν,
    graph_left_normal_ratios Q p hY h hh _ hν0 hν⟩

end DimensionFourDependence
