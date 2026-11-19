import DimensionFourDependence.ZeroInvariantFiberLine
import DimensionFourDependence.GeometricFiberNonlinearity

/-! # Excluding two zero invariants on a nonlinear geometric fiber

Homogeneity supplies the required output Euler identity. The compatible
function-field embeddings then transfer affine-line containment to every
actual geometric generic component.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- The `c=q=0` alternative of Section 3.2 for the original homogeneous
polynomial map, with its Euler and tangent data derived. -/
theorem homogeneous_zero_invariants_imply_actual_fiber_line
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) =
      algebraMap (MvPolynomial (Fin 4) K) _ (H (p 3)))
    (hc : firstFiberInvariantInChart p (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))) hY h = 0)
    (hq : secondFiberInvariant p (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))) hY h 0 = 0) :
    LiesInAffineLine
      (E := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
      (rationalCoordinate (K := K) (n := 4)) := by
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  have hNf : IsNilpotent (rationalJacobian Q) := by
    rw [rationalJacobian_polynomial H]
    exact hN.map (algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K))).mapMatrix
  have hRf : (rationalJacobian Q).rank = 3 := by
    rw [rationalJacobian_polynomial H]
    exact hrank
  exact zero_invariants_imply_actual_fiber_line Q p hY hNf hRf h hh
    (homogeneous_last_output_euler H hd hH p hY h hh) hc hq

/-- A nonlinear full-output geometric generic component cannot have
both constructed lower invariants equal to zero. -/
theorem nonlinear_geometric_component_invariants_nonzero
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (W : FiberEquationWitness (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i)))
    (h c q : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) =
      algebraMap (MvPolynomial (Fin 4) K) _ (H (W.chart 3)))
    (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) = firstFiberInvariantInChart W.chart
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))) W.independent h)
    (hq : (q : FractionRing (MvPolynomial (Fin 4) K)) = secondFiberInvariant W.chart
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (W.chart i.castSucc))) W.independent h c)
    (E : Type*) [Field E]
    [Algebra (fullOutputField (K := K) (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i))) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := fullOutputField (K := K) (fun i => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H i)))
      (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P)) : c ≠ 0 ∨ q ≠ 0 := by
  by_contra he
  obtain ⟨hc0, hq0⟩ : c = 0 ∧ q = 0 := by simpa only [not_or, not_not] using he
  subst c
  subst q
  have hactual := geometric_component_nonlinear_implies_actual_fiber_nonlinear
    (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i))
    (by rw [rationalJacobian_polynomial H]; exact hrank) W E P hP hline
  apply hactual
  apply homogeneous_zero_invariants_imply_actual_fiber_line H hd hH hN hrank W.chart W.independent h hh
  · simpa only [IntermediateField.coe_zero] using hc.symm
  · simpa only [IntermediateField.coe_zero] using hq.symm

end DimensionFourDependence
