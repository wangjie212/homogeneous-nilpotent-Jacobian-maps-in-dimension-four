import DimensionFourDependence.FiberTangentVariation
import DimensionFourDependence.TwoDirectionNormal

/-! # Dependence from a varying tangent in a fixed plane

The actual image normal kills the tangent and its derivative. These span
the fixed plane, giving two independent constant relations on the normal.
The verified rank-nullity and homogeneous dependence arguments finish.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- A rational-source pairing with a constant direction reflects to the
exact polynomial pairing, since the source embedding is injective. -/
theorem polynomial_pairing_zero_of_rational_constant_pairing
    (ν : Fin n → MvPolynomial (Fin n) K) (v : Fin n → K)
    (h : (fun i => algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (ν i))
      ⬝ᵥ (fun i => algebraMap K (FractionRing (MvPolynomial (Fin n) K)) (v i)) = 0) :
    ν ⬝ᵥ (fun i => C (v i)) = 0 := by
  have hm (a : K) : algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
      (C a) = algebraMap K (FractionRing (MvPolynomial (Fin n) K)) a := by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K)]
  apply IsFractionRing.injective (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
  simpa only [dotProduct, map_sum, map_mul, hm, map_zero] using h

variable [CharZero K]

/-- The actual normal gives component dependence for any varying
right-kernel tangent contained in a fixed constant plane. -/
theorem ImageRelationWitness.dependent_of_varying_planar_tangent
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (W : ImageRelationWitness H)
    (u : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hku : (jac H).map (algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K))) *ᵥ u = 0)
    (v w : Fin 4 → K) (hvw : LinearIndependent K ![v, w])
    (hplane : u ∈ Submodule.span (FractionRing (MvPolynomial (Fin 4) K)) (Set.range
      ![(fun i => algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (v i)),
        (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (w i))]))
    (hvar : LinearIndependent (FractionRing (MvPolynomial (Fin 4) K))
      ![(fun i => sourceVectorDerivation u (u i)), u]) : ComponentsDependent H := by
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  have hkerQ : rationalJacobian Q *ᵥ u = 0 := by
    rwa [rationalJacobian_polynomial H]
  have hDH := sourceVectorDerivation_vertical Q u hkerQ
  have hkill := constant_normal_kills_planar_tangent_space (sourceVectorDerivation u)
    (fun i => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
      (imageRelationNormal H W.equation i)) u
    (imageRelationNormal_vertical_constant H W.equation _ hDH)
    (W.kernel_pairing H hN hrank u hku) v w hplane hvar
  exact W.dependent_of_annihilated_two_space H hd hH v w hvw
    (polynomial_pairing_zero_of_rational_constant_pairing _ v hkill.1)
    (polynomial_pairing_zero_of_rational_constant_pairing _ w hkill.2)

/-- Nonlinearity of the actual fiber supplies the tangent variation
condition, over its verified exact coefficient field. -/
theorem dependent_of_nonlinear_planar_actual_tangent
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (W : FiberEquationWitness (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i)))
    (u : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (hu : u ≠ 0)
    (hku : (jac H).map (algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K))) *ᵥ u = 0)
    (v w : Fin 4 → K) (hvw : LinearIndependent K ![v, w])
    (hplane : u ∈ Submodule.span (FractionRing (MvPolynomial (Fin 4) K)) (Set.range
      ![(fun i => algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (v i)),
        (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (w i))]))
    (hline : ¬ LiesInAffineLine
      (E := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))))
      (rationalCoordinate (K := K) (n := 4))) : ComponentsDependent H := by
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  have hkerQ : rationalJacobian Q *ᵥ u = 0 := by rwa [rationalJacobian_polynomial H]
  have hkerY : rationalJacobian (fun i : Fin 3 => Q (W.chart i.castSucc)) *ᵥ u = 0 := by
    funext i
    exact congrFun hkerQ (W.chart i.castSucc)
  have hvar := nonlinear_actual_fiber_tangent_independent _ W.independent u hu hkerY hline
  obtain ⟨N⟩ := exists_image_relation_witness H hd hH hN
  exact N.dependent_of_varying_planar_tangent H hd hH hN hrank u hku v w hvw hplane hvar

end DimensionFourDependence
