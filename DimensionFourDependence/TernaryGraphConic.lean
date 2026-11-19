import DimensionFourDependence.TernaryGraphLineDirection
import DimensionFourDependence.TernaryLineConstantPlaneExclusion
import DimensionFourDependence.TernaryIndependentOutputChart

/-! # The actual projected ternary curve is the invariant conic -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 2000000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)
local notation "x" => (rationalCoordinate (K := K) (n := 3))

/-- A normalized independent nilpotent map has no linear projected
generic curve. Its quadratic invariant itself generates the full
affine relation ideal in every chart with two independent outputs. -/
theorem normalized_ternary_independent_chart_constructs_invariant_conic
    (H : Fin 3 → R₃) (h0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (H i) = 0)
    (hind : ¬ComponentsDependent H) (hN : IsNilpotent (jac H))
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y)
    (hpair : ∀ i : Fin 2, Y i = ι (H i.castSucc))
    (w : coefficientField (K := K) Y) (hw : (w : F) = ι (H 2)) :
    ∃ s τ : coefficientField (K := K) Y,
      (s : F) = ternaryGraphPlaneValue Y hY w ∧
      (τ : F) = ternaryGraphQuadraticValue Y hY w s ∧
      let Q := ternaryGraphQuadraticEquation Y hY w s τ
      fiberVanishingIdeal (L := coefficientField (K := K) Y)
        (fun i : Fin 2 => x i.castSucc) = Ideal.span {Q} ∧
      Irreducible Q ∧ Q.totalDegree = 2 := by
  obtain ⟨s, τ, P, C₀, hs, hτ, hI, hP, hd, hdiv, _, _⟩ :=
    normalized_ternary_map_constructs_generic_curve.{u, u} H h0 hind hN Y hY hpair w hw
  have hdP : P.totalDegree = 2 := by
    refine hd.resolve_left ?_
    intro hline
    obtain ⟨D, l, hD, hl, hH, hInv, hPlane⟩ :=
      ternary_linear_graph_constructs_invariant_direction_in_constant_plane
        H h0 hind hN Y hY hpair w hw s hs P hI hline
    exact hind (invariant_ternary_line_in_constant_direction_plane_componentsDependent
      H h0 hN D hD hH hInv l hl hPlane)
  let Q := ternaryGraphQuadraticEquation Y hY w s τ
  have hQ0 : Q ≠ 0 := ternaryGraphQuadraticEquation_ne_zero Y hY w s τ
    (closed_field_normalized_ternary_graph_hessian_ne_zero H h0 hind Y hY hpair w hw)
  obtain ⟨M, hM⟩ := hdiv
  have hM0 : M ≠ 0 := by
    intro h
    apply hQ0
    rw [show Q = P * M from hM, h, mul_zero]
  have hQdeg : Q.totalDegree = 2 + M.totalDegree := by
    rw [show Q = P * M from hM, totalDegree_mul_of_isDomain hP.ne_zero hM0, hdP]
  have hle := ternaryGraphQuadraticEquation_totalDegree_le Y hY w s τ
  change Q.totalDegree ≤ 2 at hle
  have hMdeg : M.totalDegree = 0 := by omega
  have hMc := totalDegree_eq_zero_iff_eq_C.mp hMdeg
  have hMc0 : M.coeff 0 ≠ 0 := by
    intro h
    apply hM0
    rw [hMc, h, map_zero]
  have hMu : IsUnit M := by
    rw [hMc]
    exact (isUnit_iff_ne_zero.mpr hMc0).map C
  have hIQ : fiberVanishingIdeal (L := coefficientField (K := K) Y)
      (fun i : Fin 2 => x i.castSucc) = Ideal.span {Q} := by
    rw [show Q = P * M from hM, Ideal.span_singleton_mul_right_unit hMu P]
    exact hI
  have hQ : Irreducible Q := ((Ideal.span_singleton_prime hQ0).mp
    (hIQ ▸ (inferInstance : (fiberVanishingIdeal (L := coefficientField (K := K) Y)
      (fun i : Fin 2 => x i.castSucc)).IsPrime))).irreducible
  exact ⟨s, τ, hs, hτ, hIQ, hQ, by
    change Q.totalDegree = 2
    rw [hQdeg, hMdeg, add_zero]⟩

end DimensionFourDependence
