import DimensionFourDependence.FullOutputField

/-! # Constructing actual invariant coefficients for any actual fiber witness

Every independent output chart of a checked fiber-equation witness
supplies its actual last output and all three actual invariant expressions
inside the corresponding coefficient field. The coefficients are
constructed for that witness, avoiding an assumption that independently
chosen auxiliary charts agree.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- Any actual fiber-equation witness supplies all coefficient-field
elements and their exact defining equations from the original map. -/
theorem fiberEquationWitness_exists_invariant_coefficients
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3)
    (W : FiberEquationWitness (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i))) :
    ∃ h c q k : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))),
      (h : FractionRing (MvPolynomial (Fin 4) K)) =
        algebraMap (MvPolynomial (Fin 4) K) _ (H (W.chart 3)) ∧
      (c : FractionRing (MvPolynomial (Fin 4) K)) = firstFiberInvariantInChart W.chart
        (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
          (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))) W.independent h ∧
      (q : FractionRing (MvPolynomial (Fin 4) K)) = secondFiberInvariant W.chart
        (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
          (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))) W.independent h c ∧
      (k : FractionRing (MvPolynomial (Fin 4) K)) = thirdFiberInvariant W.chart
        (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
          (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))) W.independent h c q := by
  let V : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  have hVN : IsNilpotent (rationalJacobian V) := by
    rw [rationalJacobian_polynomial H]
    exact hN.map (algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K))).mapMatrix
  have hVr : (rationalJacobian V).rank = 3 := by
    rw [rationalJacobian_polynomial H]
    exact hrank
  let Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K) := fun i => V (W.chart i.castSucc)
  let h : coefficientField (K := K) Y := ⟨V (W.chart 3), mem_algebraicClosure_iff.mpr
    (outputs_algebraic_over_independent_triple V hVr W.chart W.independent (W.chart 3))⟩
  let c : coefficientField (K := K) Y :=
    ⟨firstFiberInvariantInChart W.chart Y W.independent h,
      firstFiberInvariantInChart_mem_of_rank_three V hVN hVr W.chart W.independent h rfl⟩
  let q : coefficientField (K := K) Y :=
    ⟨secondFiberInvariant W.chart Y W.independent h c,
      secondFiberInvariant_mem_of_nilpotent_rank_three V hVN hVr W.chart W.independent h c rfl rfl⟩
  let k : coefficientField (K := K) Y :=
    ⟨thirdFiberInvariant W.chart Y W.independent h c q,
      thirdFiberInvariant_mem_of_nilpotent_rank_three V hVN hVr W.chart W.independent h c q rfl rfl rfl⟩
  exact ⟨h, c, q, k, rfl, rfl, rfl, rfl⟩

end DimensionFourDependence
