import DimensionFourDependence.OriginalGaussGraphCoordinates

/-! # Original normal rulings and graph ruling equations agree

Writing the normal as its last chart coordinate times the graph normal
identifies the normal and differentiated-normal equations. The scalar's
derivative contributes only a multiple of the first graph equation.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

section LinearAlgebra

variable {K F κ : Type*} [Field K] [Field F] [Algebra K F] [Field κ]

/-- The first graph equation and the differentiated graph-gradient
equation imply both original normal ruling equations after every field
homomorphism. No parameter-change or normalization scalar is assumed. -/
theorem normal_parameter_ruling_of_graph_equations
    (D : Derivation K F F) (ν : Fin 4 → F) (A : Fin 3 → F)
    (p : Equiv.Perm (Fin 4))
    (hν : ∀ i, ν (p i.castSucc) = -A i * ν (p 3))
    (f : F →+* κ) (b : Fin 4 → κ)
    (hlinear : b (p 3) = ∑ i : Fin 3, f (A i) * b (p i.castSucc))
    (hruling : ∑ i : Fin 3, f (D (A i)) * b (p i.castSucc) = 0) :
    (normalRulingMatrix D ν).map f *ᵥ b = 0 := by
  have hνD (i : Fin 3) : D (ν (p i.castSucc)) =
      -(D (A i) * ν (p 3) + A i * D (ν (p 3))) := by
    rw [hν, D.leibniz, map_neg]
    simp only [smul_eq_mul]
    ring
  have hsum : (∑ i : Fin 3, f (ν (p i.castSucc)) * b (p i.castSucc)) =
      -(f (ν (p 3)) * ∑ i : Fin 3, f (A i) * b (p i.castSucc)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hν, map_mul, map_neg]
    ring
  have hsumD : (∑ i : Fin 3, f (D (ν (p i.castSucc))) * b (p i.castSucc)) =
      -(f (ν (p 3)) * (∑ i : Fin 3, f (D (A i)) * b (p i.castSucc)) +
        f (D (ν (p 3))) * ∑ i : Fin 3, f (A i) * b (p i.castSucc)) := by
    calc
      _ = ∑ i : Fin 3,
          -(f (ν (p 3)) * (f (D (A i)) * b (p i.castSucc)) +
            f (D (ν (p 3))) * (f (A i) * b (p i.castSucc))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hνD, map_neg, map_add, map_mul, map_mul]
        ring
      _ = _ := by
        rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  funext r
  fin_cases r
  · change (∑ j, f (ν j) * b j) = 0
    rw [← Equiv.sum_comp p (fun j => f (ν j) * b j), Fin.sum_univ_castSucc]
    change (∑ i : Fin 3, f (ν (p i.castSucc)) * b (p i.castSucc)) + f (ν (p 3)) * b (p 3) = 0
    rw [hsum, hlinear]
    ring
  · change (∑ j, f (D (ν j)) * b j) = 0
    rw [← Equiv.sum_comp p (fun j => f (D (ν j)) * b j), Fin.sum_univ_castSucc]
    change (∑ i : Fin 3, f (D (ν (p i.castSucc))) * b (p i.castSucc)) + f (D (ν (p 3))) * b (p 3) = 0
    rw [hsumD, hruling, hlinear]
    ring

end LinearAlgebra

universe u

variable {K : Type u} [Field K] [CharZero K]

attribute [local instance] coefficientFieldScalarTower

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

/-- The original normalized normal and the original-parameter graph
slope satisfy the actual graph coordinate identity in the original
rational function field, before every coefficient extension. -/
theorem original_gauss_normal_graph_coordinate_relation
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3))) (i : Fin 3) :
    gaussParameterNormal H I e (p i.castSucc) =
      -originalGaussCoefficientGraphSlope H I p hY e h hh i * gaussParameterNormal H I e (p 3) := by
  let f := gaussParameterSourceHom H I e
  apply f.injective
  change gaussParameterSourceHom H I e _ = gaussParameterSourceHom H I e _
  rw [map_mul, map_neg, gaussParameterSourceHom_normal, gaussParameterSourceHom_normal]
  have hA : gaussParameterSourceHom H I e (originalGaussCoefficientGraphSlope H I p hY e h hh i) =
      (coefficientPartial _ hY i h : FractionRing (MvPolynomial (Fin 4) K)) := by
    rw [← originalGaussCoefficientParameterHom_source_value H hrank I p hY e,
      originalGaussCoefficientGraphSlope_value]
  rw [hA]
  obtain ⟨hlast, hcoord⟩ := I.gauss_chart_ratios H p hY h hh
  have hi := (div_eq_iff hlast).mp (hcoord i)
  simp only [fiberGradient] at hi
  change rationalImageNormal H I.equation (p i.castSucc) /
      rationalImageNormal H I.equation (imageNormalPivot H I) = _
  rw [hi]
  ring

end DimensionFourDependence
