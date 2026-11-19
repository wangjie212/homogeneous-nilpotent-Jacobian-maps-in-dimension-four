import DimensionFourDependence.TernaryChartCoefficientTransport
import DimensionFourDependence.TernaryGraphAffineChartChange
import DimensionFourDependence.TransportedAffineCurveRelation

/-! # Transverse original frames preserve the conic at infinity exactly -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2250000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)
local notation "x" => (rationalCoordinate (K := K) (n := 3))

/-- The actual fraction-field values of the first two components. -/
noncomputable abbrev ternaryRationalOutputPair (H : Fin 3 → R₃) : Fin 2 → F :=
  fun i => ι (H i.castSucc)

/-- The linear part of the projected affine change gives the exact
leading relation of the transformed conic, up to a nonzero scalar.
The coefficient-field equivalence is induced by the source change. -/
theorem ternary_conic_transverse_chart_leading_relation_associated
    (T S : Matrix (Fin 3) (Fin 3) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin 3 → R₃) (hN : IsNilpotent (jac H))
    (hY : AlgebraicIndependent K (ternaryRationalOutputPair H))
    (hY' : AlgebraicIndependent K (ternaryRationalOutputPair (linearPolynomialConjugate T S H)))
    (w s : coefficientField (K := K) (ternaryRationalOutputPair H))
    (hs : (s : F) = ternaryGraphPlaneValue (ternaryRationalOutputPair H) hY w)
    (P : MvPolynomial (Fin 2) (coefficientField (K := K) (ternaryRationalOutputPair H)))
    (hP : Irreducible P) (hdP : P.totalDegree = 2)
    (hI : fiberVanishingIdeal (L := coefficientField (K := K) (ternaryRationalOutputPair H))
      (fun i : Fin 2 => x i.castSucc) = Ideal.span {P})
    (Q : MvPolynomial (Fin 2) (coefficientField (K := K)
      (ternaryRationalOutputPair (linearPolynomialConjugate T S H))))
    (hQ : aeval (fun i : Fin 2 => x i.castSucc) Q = 0) (hdQ : Q.totalDegree = 2) :
    let Y := ternaryRationalOutputPair H
    let L := coefficientField (K := K) Y
    let M := coefficientField (K := K) (ternaryRationalOutputPair (linearPolynomialConjugate T S H))
    let A : Matrix (Fin 2) (Fin 2) L := fun i => ternaryGraphRestrictedCovector
      (coefficientPartial Y hY 0 w) (coefficientPartial Y hY 1 w) (S i.castSucc)
    A.det ≠ 0 → ∃ (α : L ≃ₐ[K] M) (c : L), c ≠ 0 ∧
      aeval (linearPolynomialMap A) (homogeneousComponent 2 (MvPolynomial.map α.symm.toRingHom Q)) =
        C c * homogeneousComponent 2 P := by
  let Y := ternaryRationalOutputPair H
  let L := coefficientField (K := K) Y
  let M := coefficientField (K := K) (ternaryRationalOutputPair (linearPolynomialConjugate T S H))
  let : IsScalarTower K L F := coefficientFieldScalarTower Y
  let e := matrixSourceFractionEquiv T S hTS hST
  let p := coefficientPartial Y hY 0 w
  let q := coefficientPartial Y hY 1 w
  let A : Matrix (Fin 2) (Fin 2) L := fun i => ternaryGraphRestrictedCovector p q (S i.castSucc)
  let g := fun i : Fin 2 => ternaryGraphProjectedCoordinatePolynomial p q s (S i.castSucc)
  dsimp only
  intro hA
  have hm : (L.restrictScalars K).map e.toAlgHom = M.restrictScalars K :=
    ternary_chart_coefficientField_map_linearPolynomialConjugate T S hTS hST H hN hY hY'
  let α : L ≃ₐ[K] M := (IntermediateField.equivMap (L.restrictScalars K) e.toAlgHom).trans
    (IntermediateField.equivOfEq hm)
  have hα (c : L) : e (algebraMap L F c) = algebraMap M F (α c) := rfl
  have hplane : x 2 = algebraMap L F s + algebraMap L F p * x 0 + algebraMap L F q * x 1 := by
    change x 2 = (s : F) + (p : F) * x 0 + (q : F) * x 1
    change (s : F) = x 2 - (p : F) * x 0 - (q : F) * x 1 at hs
    linear_combination -hs
  have hg (i : Fin 2) : e (aeval (fun j : Fin 2 => x j.castSucc) (g i)) = x i.castSucc :=
    ternaryGraphProjectedCoordinatePolynomial_source_value T S hTS hST p q s hplane i
  have hd (i : Fin 2) : (g i).totalDegree ≤ 1 :=
    ternaryGraphProjectedCoordinatePolynomial_totalDegree_le p q s _
  have hlin := ternaryGraphProjectedCoordinatePolynomial_leading_pullback_injective p q s
    (fun i : Fin 2 => S i.castSucc) hA
  obtain ⟨c, hc, he⟩ := affine_chart_change_quadratic_leading_relation_associated
    α.toRingEquiv e.toRingEquiv hα (fun i : Fin 2 => x i.castSucc) (fun i : Fin 2 => x i.castSucc)
    g hg hd hlin P hP hdP hI Q hQ hdQ
  have hEq : (fun i => homogeneousComponent 1 (g i)) = linearPolynomialMap A := by
    funext i
    exact ternaryGraphProjectedCoordinatePolynomial_leading_component p q s (S i.castSucc)
  rw [hEq] at he
  exact ⟨α, c, hc, he⟩

end DimensionFourDependence
