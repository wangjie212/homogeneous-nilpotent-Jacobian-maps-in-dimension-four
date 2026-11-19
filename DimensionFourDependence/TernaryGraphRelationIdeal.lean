import DimensionFourDependence.TernaryGraphCoordinateField
import DimensionFourDependence.TernaryGraphQuadraticEquation
import DimensionFourDependence.AffinePrincipalCone
import DimensionFourDependence.FiberPrimeDimension

/-! # The principal relation ideal of the actual projected ternary curve -/

namespace DimensionFourDependence

open MvPolynomial

variable {L : Type*} [Field L]

/-- A nonmaximal prime in the affine plane has height at most one. -/
theorem affine_two_prime_height_le_one
    (I : Ideal (MvPolynomial (Fin 2) L)) [I.IsPrime] (hnm : ¬ I.IsMaximal) :
    I.height ≤ 1 := by
  have hd : ringKrullDim (MvPolynomial (Fin 2) L) = 2 := by simp
  have : FiniteRingKrullDim (MvPolynomial (Fin 2) L) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨by rw [hd]; simp, by
      rw [hd]
      change ((2 : ℕ∞) : WithBot ℕ∞) ≠ ⊤
      exact fun h => ENat.natCast_ne_top 2 (WithBot.coe_eq_top.mp h)⟩
  have hb : (I.height : WithBot ℕ∞) ≤ 2 := by
    simpa only [hd] using (Ideal.height_le_ringKrullDim_of_isPrime (I := I))
  have hle : I.height ≤ 2 := WithBot.coe_le_coe.mp hb
  have hne : I.height ≠ 2 := by
    intro he
    apply hnm
    apply Ideal.isMaximal_of_height_eq_ringKrullDim
    simp only [he, hd, WithBot.coe_ofNat]
  exact ENat.lt_two_iff.mp (lt_of_le_of_ne hle hne)

variable {K : Type*} [Field K] [CharZero K]

local notation "F" => FractionRing (MvPolynomial (Fin 3) K)
local notation "x" => (fun i : Fin 2 => rationalCoordinate (K := K) (n := 3) (Fin.castSucc i))

/-- The actual projected curve is cut out by one irreducible generator
of degree one or two. Its relation ideal includes every polynomial
relation over the actual coefficient field. -/
theorem ternary_graph_relation_ideal_has_linear_or_quadratic_generator
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y)
    (w s τ : coefficientField (K := K) Y)
    (hs : (s : F) = ternaryGraphPlaneValue Y hY w)
    (hτ : (τ : F) = ternaryGraphQuadraticValue Y hY w s)
    (hHess : ternaryGraphHessian Y hY w ≠ 0) :
    ∃ P : MvPolynomial (Fin 2) (coefficientField (K := K) Y),
      fiberVanishingIdeal (L := coefficientField (K := K) Y) x = Ideal.span {P} ∧
      Irreducible P ∧ (P.totalDegree = 1 ∨ P.totalDegree = 2) ∧
      P ∣ ternaryGraphQuadraticEquation Y hY w s τ := by
  let E := coefficientField (K := K) Y
  let I := fiberVanishingIdeal (L := E) x
  let Q := ternaryGraphQuadraticEquation Y hY w s τ
  have hQ : Q ∈ I := ternaryGraphQuadraticEquation_aeval Y hY w s τ hτ
  have hQ0 : Q ≠ 0 := ternaryGraphQuadraticEquation_ne_zero Y hY w s τ hHess
  have hNM : ¬ I.IsMaximal := fiberVanishingIdeal_not_isMaximal x
    (ternary_graph_coordinate_field_eq_top Y hY w s hs)
    (by rw [ternary_coefficientField_trdeg_eq_one Y hY]; exact one_ne_zero)
  obtain ⟨P, hI⟩ := prime_height_le_one_exists_generator I (affine_two_prime_height_le_one I hNM)
  have hPQ : P ∣ Q := Ideal.mem_span_singleton.mp (hI ▸ hQ)
  have hP0 : P ≠ 0 := by
    intro h
    exact hQ0 (zero_dvd_iff.mp (h ▸ hPQ))
  have hP : Irreducible P := ((Ideal.span_singleton_prime hP0).mp
    (hI ▸ (inferInstance : I.IsPrime))).irreducible
  have hpEval : aeval x P = 0 := by
    change P ∈ I
    rw [hI]
    exact Ideal.subset_span (by simp)
  have hpPos := totalDegree_pos_of_aeval_zero x P hP0 hpEval
  obtain ⟨B, hB⟩ := hPQ
  have hB0 : B ≠ 0 := by
    intro h
    apply hQ0
    rw [hB, h, mul_zero]
  have hd : Q.totalDegree = P.totalDegree + B.totalDegree :=
    hB ▸ totalDegree_mul_of_isDomain hP0 hB0
  have hle : Q.totalDegree ≤ 2 := ternaryGraphQuadraticEquation_totalDegree_le Y hY w s τ
  exact ⟨P, hI, hP, by omega, ⟨B, hB⟩⟩

end DimensionFourDependence
