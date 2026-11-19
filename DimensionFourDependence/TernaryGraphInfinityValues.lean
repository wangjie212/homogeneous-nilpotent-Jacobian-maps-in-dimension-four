import DimensionFourDependence.AffineSubstitutionLeadingValue
import DimensionFourDependence.QuadraticEulerComparison
import DimensionFourDependence.FiberCoordinateRing
import DimensionFourDependence.ProjectiveLineAtlasPoints

/-! # Directions of the projected curve are zeros of the original top form -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 1700000

variable {K L A F : Type*} [Field K] [Field L] [Field A] [Field F]
  [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]
  [Algebra L F] [Algebra K F] [IsScalarTower K L F]

/-- The three original coordinates on an affine graph over two coordinates. -/
noncomputable def ternaryGraphCoordinatePolynomials (a b s : L) : Fin 3 → MvPolynomial (Fin 2) L :=
  ![X 0, X 1, C s + C a * X 0 + C b * X 1]

theorem ternaryGraphCoordinatePolynomials_totalDegree_le (a b s : L) (i : Fin 3) :
    (ternaryGraphCoordinatePolynomials a b s i).totalDegree ≤ 1 := by
  fin_cases i
  · exact (totalDegree_X _).le
  · exact (totalDegree_X _).le
  · change (C s + C a * X (0 : Fin 2) + C b * X 1).totalDegree ≤ 1
    have ha : (C a * X (0 : Fin 2)).totalDegree ≤ 1 := by
      simpa using totalDegree_mul (C a) (X (0 : Fin 2))
    have hb : (C b * X (1 : Fin 2)).totalDegree ≤ 1 := by
      simpa using totalDegree_mul (C b) (X (1 : Fin 2))
    apply (totalDegree_add _ _).trans (max_le _ hb)
    apply (totalDegree_add _ _).trans (max_le _ ha)
    simp

theorem ternaryGraphCoordinatePolynomials_aeval (a b s : L) (e : Fin 2 → F) :
    (fun i => aeval e (ternaryGraphCoordinatePolynomials a b s i)) =
      ![e 0, e 1, algebraMap L F s + algebraMap L F a * e 0 + algebraMap L F b * e 1] := by
  funext i
  fin_cases i <;> simp [ternaryGraphCoordinatePolynomials]

/-- The plane's points at infinity use only the linear part of its graph. -/
theorem ternaryGraphCoordinatePolynomials_leading_aeval (a b s : L) (e : Fin 2 → A) :
    (fun i => aeval e (homogeneousComponent 1 (ternaryGraphCoordinatePolynomials a b s i))) =
      ![e 0, e 1, algebraMap L A a * e 0 + algebraMap L A b * e 1] := by
  have hC : homogeneousComponent 1 (C s : MvPolynomial (Fin 2) L) = 0 :=
    homogeneousComponent_eq_zero _ _ (by simp)
  have hX (i : Fin 2) : homogeneousComponent 1 (X i : MvPolynomial (Fin 2) L) = X i :=
    homogeneousComponent_eq_self (isHomogeneous_X L i)
  funext i
  fin_cases i
  · change aeval e (homogeneousComponent 1 (X 0 : MvPolynomial (Fin 2) L)) = e 0
    rw [hX, aeval_X]
  · change aeval e (homogeneousComponent 1 (X 1 : MvPolynomial (Fin 2) L)) = e 1
    rw [hX, aeval_X]
  · change aeval e (homogeneousComponent 1 (C s + C a * X 0 + C b * X 1)) = _
    simp only [map_add, homogeneousComponent_C_mul, hC, hX, zero_add, map_mul, aeval_C, aeval_X]
    rfl

private theorem ternary_graph_direction_annihilates_top
    (a b s c : L) (x : Fin 2 → F) (H : MvPolynomial (Fin 3) L)
    (hconst : aeval (![x 0, x 1, algebraMap L F s + algebraMap L F a * x 0 + algebraMap L F b * x 1] :
      Fin 3 → F) H = algebraMap L F c)
    (P : MvPolynomial (Fin 2) L) (hP : P ≠ 0)
    (hideal : fiberVanishingIdeal (L := L) x = Ideal.span {P})
    {d : ℕ} (hd : 0 < d) (hH : H.totalDegree ≤ d) (e : Fin 2 → A)
    (he : aeval e (homogeneousComponent P.totalDegree P) = 0) :
    aeval (![e 0, e 1, algebraMap L A a * e 0 + algebraMap L A b * e 1] : Fin 3 → A)
      (homogeneousComponent d H) = 0 := by
  let G := ternaryGraphCoordinatePolynomials a b s
  let Q := aeval G H - C c
  have hG (i : Fin 3) : (G i).totalDegree ≤ 1 := ternaryGraphCoordinatePolynomials_totalDegree_le a b s i
  have hv : aeval x Q = 0 := by
    change aeval x (aeval G H - C c) = 0
    have hcoord : (fun i => aeval x (G i)) = _ := ternaryGraphCoordinatePolynomials_aeval a b s x
    simp only [map_sub, aeval_C, comp_aeval_apply, hcoord, hconst, sub_self]
  have hQ : P ∣ Q := by
    change Q ∈ fiberVanishingIdeal (L := L) x at hv
    rw [hideal] at hv
    exact Ideal.mem_span_singleton.mp hv
  have hQdeg : Q.totalDegree ≤ d := (totalDegree_sub_C_le _ _).trans
    ((totalDegree_aeval_le_of_affine G hG H).trans hH)
  have htop := homogeneous_value_eq_zero_of_divisor_direction P Q hP hQ hQdeg e he
  have hc : homogeneousComponent d (C c : MvPolynomial (Fin 2) L) = 0 :=
    homogeneousComponent_eq_zero _ _ (by simpa using hd)
  change aeval e (homogeneousComponent d (aeval G H - C c)) = 0 at htop
  simp only [map_sub, hc, sub_zero, affine_substitution_homogeneous_value G hG H hH] at htop
  have hcoord := ternaryGraphCoordinatePolynomials_leading_aeval a b s e
  exact (congrArg (fun y : Fin 3 → A => aeval y (homogeneousComponent d H)) hcoord).symm.trans htop

/-- A direction of the actual plane curve satisfies the highest
homogeneous equation of each original polynomial constant on the curve. -/
theorem ternary_graph_direction_annihilates_original_top
    (a b s c : L) (x : Fin 2 → F) (H : MvPolynomial (Fin 3) K)
    (hconst : aeval (![x 0, x 1, algebraMap L F s + algebraMap L F a * x 0 + algebraMap L F b * x 1] :
      Fin 3 → F) H = algebraMap L F c)
    (P : MvPolynomial (Fin 2) L) (hP : P ≠ 0)
    (hideal : fiberVanishingIdeal (L := L) x = Ideal.span {P})
    {d : ℕ} (hd : 0 < d) (hH : H.totalDegree ≤ d) (e : Fin 2 → A)
    (he : aeval e (homogeneousComponent P.totalDegree P) = 0) :
    aeval (![e 0, e 1, algebraMap L A a * e 0 + algebraMap L A b * e 1] : Fin 3 → A)
      (homogeneousComponent d H) = 0 := by
  let H' := MvPolynomial.map (algebraMap K L) H
  have hmapdeg : H'.totalDegree ≤ H.totalDegree := by
    unfold totalDegree
    exact Finset.sup_mono (support_map_subset (algebraMap K L) H)
  have hdeg := hmapdeg.trans hH
  have hconst' : aeval (![x 0, x 1, algebraMap L F s + algebraMap L F a * x 0 + algebraMap L F b * x 1] :
      Fin 3 → F) H' = algebraMap L F c := by
    exact (aeval_map_algebra_extension (E := L) H _).trans hconst
  have heval := ternary_graph_direction_annihilates_top a b s c x H' hconst' P hP hideal hd hdeg e he
  change aeval _ (homogeneousComponent d (MvPolynomial.map (algebraMap K L) H)) = 0 at heval
  rw [homogeneous_component_coefficient_map, aeval_map_algebra_extension (E := L)] at heval
  exact heval

end DimensionFourDependence
