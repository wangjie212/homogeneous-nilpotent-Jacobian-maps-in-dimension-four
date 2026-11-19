import DimensionFourDependence.TernaryGraphCurve
import DimensionFourDependence.ModifiedCubicFiberBoundary

/-! # The linear projected curve supplies an invariant direction in a constant plane -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2200000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)
local notation "x" => (rationalCoordinate (K := K) (n := 3))

private theorem binary_linear_kernel_scale {E : Type*} [Field E] {a b u v : E}
    (hab : a ≠ 0 ∨ b ≠ 0) (huv : u ≠ 0 ∨ v ≠ 0) (he : a * u + b * v = 0) :
    ∃ k : E, k ≠ 0 ∧ u = k * b ∧ v = k * (-a) := by
  by_cases hb : b = 0
  · have ha := hab.resolve_right (fun h => h hb)
    have hu : u = 0 := by
      rw [hb, zero_mul, add_zero] at he
      exact (mul_eq_zero.mp he).resolve_left ha
    have hv := huv.resolve_left (fun h => h hu)
    refine ⟨v / (-a), div_ne_zero hv (neg_ne_zero.mpr ha), ?_, ?_⟩
    · rw [hu, hb, mul_zero]
    · exact (div_mul_cancel₀ _ (neg_ne_zero.mpr ha)).symm
  · have hu : u ≠ 0 := by
      intro hz
      rw [hz, mul_zero, zero_add] at he
      exact huv.resolve_left (fun h => h hz) ((mul_eq_zero.mp he).resolve_left hb)
    refine ⟨u / b, div_ne_zero hu hb, (div_mul_cancel₀ _ hb).symm, ?_⟩
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hb).mpr
    linear_combination he

/-- If the projected curve is a line, its original embedded direction
can be chosen with invariant entries and lies in an original constant
plane. The derivation still annihilates every original output. -/
theorem ternary_linear_graph_constructs_invariant_direction_in_constant_plane
    (H : Fin 3 → R₃) (h0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (H i) = 0)
    (hind : ¬ComponentsDependent H) (hN : IsNilpotent (jac H))
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y)
    (hpair : ∀ i : Fin 2, Y i = ι (H i.castSucc))
    (w : coefficientField (K := K) Y) (hw : (w : F) = ι (H 2))
    (s : coefficientField (K := K) Y) (hs : (s : F) = ternaryGraphPlaneValue Y hY w)
    (P : MvPolynomial (Fin 2) (coefficientField (K := K) Y))
    (hI : fiberVanishingIdeal (L := coefficientField (K := K) Y)
      (fun i : Fin 2 => x i.castSucc) = Ideal.span {P})
    (hdeg : P.totalDegree = 1) :
    ∃ (D : Derivation K F F) (l : Fin 3 → K), D ≠ 0 ∧ l ≠ 0 ∧
      (∀ i, D (ι (H i)) = 0) ∧ (∀ i, D (D (x i)) = 0) ∧
      ∑ i, algebraMap K F (l i) * D (x i) = 0 := by
  let L := coefficientField (K := K) Y
  let : IsScalarTower K L F := coefficientFieldScalarTower Y
  let D := ternaryJacobianDerivation (K := K) (Y 0) (Y 1)
  let a : Fin 2 → L := fun i => (pderiv i P).coeff 0
  let b : L := P.coeff 0
  let p := coefficientPartial Y hY 0 w
  let q := coefficientPartial Y hY 1 w
  have hDl (c : L) : D (c : F) = 0 :=
    vertical_derivation_kills_coefficient_field Y D (ternaryJacobianDerivation_kills_pair Y) c
  have hD0 : D ≠ 0 := sourceVectorDerivation_ne_zero _ (ternaryJacobianDirection_ne_zero Y hY)
  have hP : P = C b + linearFormPolynomial a := affine_polynomial_expansion P hdeg.le
  have hLead : homogeneousComponent 1 P = linearFormPolynomial a := by
    rw [hP, map_add, homogeneousComponent_eq_zero _ _ (by simp [totalDegree_C]),
      homogeneousComponent_eq_self (linearFormPolynomial_homogeneous a), zero_add]
  have ha : a 0 ≠ 0 ∨ a 1 ≠ 0 := by
    by_contra h
    push Not at h
    have he : (P : MvPolynomial (Fin 2) L) = C b := by
      rw [hP]
      simp [linearFormPolynomial, Fin.sum_univ_two, h.1, h.2]
    rw [he, totalDegree_C] at hdeg
    omega
  have hzP : aeval (fun i : Fin 2 => x i.castSucc) P = 0 := by
    change P ∈ fiberVanishingIdeal (L := L) (fun i : Fin 2 => x i.castSucc)
    rw [hI]
    exact Ideal.subset_span (by simp)
  rw [hP, map_add, aeval_C] at hzP
  have hline : (b : F) + (a 0 : F) * x 0 + (a 1 : F) * x 1 = 0 := by
    have he : aeval (fun i : Fin 2 => x i.castSucc) (linearFormPolynomial a) =
        (a 0 : F) * x 0 + (a 1 : F) * x 1 := by
      simp [linearFormPolynomial, Fin.sum_univ_two, IntermediateField.algebraMap_apply]
    rw [he] at hzP
    change (b : F) + ((a 0 : F) * x 0 + (a 1 : F) * x 1) = 0 at hzP
    linear_combination hzP
  have hDa : (a 0 : F) * D (x 0) + (a 1 : F) * D (x 1) = 0 := by
    have he := congrArg D hline
    change D ((b : F) + (a 0 : F) * x 0 + (a 1 : F) * x 1) = D 0 at he
    simpa only [map_add, map_zero, Derivation.leibniz, smul_eq_mul, hDl, mul_zero, add_zero, zero_add] using he
  have hDz : D (x 2) = (p : F) * D (x 0) + (q : F) * D (x 1) := by
    have he := congrArg D hs
    change D (s : F) = D (x 2 - (p : F) * x 0 - (q : F) * x 1) at he
    simp only [hDl, map_sub, Derivation.leibniz, smul_eq_mul, mul_zero, add_zero] at he
    linear_combination -he
  have hDxy : D (x 0) ≠ 0 ∨ D (x 1) ≠ 0 := by
    by_contra h
    push Not at h
    apply hD0
    apply derivation_ext_rational
    intro i
    fin_cases i
    · exact h.1
    · exact h.2
    · change D (x 2) = 0
      rw [hDz, h.1, h.2, mul_zero, mul_zero, add_zero]
  have haF : (a 0 : F) ≠ 0 ∨ (a 1 : F) ≠ 0 := ha.imp
    (fun h => by simpa only [map_zero, IntermediateField.algebraMap_apply] using
      (algebraMap L F).injective.ne h)
    (fun h => by simpa only [map_zero, IntermediateField.algebraMap_apply] using
      (algebraMap L F).injective.ne h)
  obtain ⟨k, hk, hDx, hDy⟩ := binary_linear_kernel_scale haF hDxy hDa
  let e : Fin 2 → L := ![a 1, -a 0]
  let v : Fin 3 → L := ![e 0, e 1, p * e 0 + q * e 1]
  let V := sourceVectorDerivation (fun i => (v i : F))
  have hDV : D = k • V := by
    apply derivation_ext_rational
    intro i
    simp only [Derivation.smul_apply, smul_eq_mul, V, sourceVectorDerivation_coordinate]
    fin_cases i
    · exact hDx
    · exact hDy
    · change D (x 2) = k * (v 2 : F)
      rw [hDz, hDx, hDy]
      change (p : F) * (k * (a 1 : F)) + (q : F) * (k * (-(a 0 : F))) =
        k * ((p : F) * (a 1 : F) + (q : F) * (-(a 0 : F)))
      ring
  have hVL (c : L) : V (c : F) = 0 := by
    have he := hDl c
    rw [hDV] at he
    exact (mul_eq_zero.mp he).resolve_left hk
  have hVH (i : Fin 3) : V (ι (H i)) = 0 := by
    have he : D (ι (H i)) = 0 := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change D (ι (H 2)) = 0
        rw [← hw]
        exact hDl w
      · rw [← hpair]
        exact ternaryJacobianDerivation_kills_pair Y j
    rw [hDV] at he
    exact (mul_eq_zero.mp he).resolve_left hk
  have hVI (i : Fin 3) : V (V (x i)) = 0 := by
    rw [sourceVectorDerivation_coordinate]
    exact hVL (v i)
  have hV0 : V ≠ 0 := by
    intro hh
    rw [hDV, hh, smul_zero] at hD0
    exact hD0 rfl
  have hDir : aeval e (homogeneousComponent P.totalDegree P) = 0 := by
    rw [hdeg, hLead]
    simp [linearFormPolynomial, Fin.sum_univ_two, e] <;> ring
  have hP0 : P ≠ 0 := by intro h; simp [h] at hdeg
  obtain ⟨C₀, hC, hCover⟩ := ternary_graph_generator_direction_cover.{u, u}
    H h0 hind hN Y hY hpair w hw s hs P hP0 hI
  obtain ⟨l, hl, hlz⟩ := hCover L e hDir
  have hlv : aeval v (linearFormPolynomial l) = 0 := by
    change aeval (![e 0, e 1, algebraMap L L p * e 0 + algebraMap L L q * e 1] :
      Fin 3 → L) (linearFormPolynomial l) = 0 at hlz
    simpa only [Algebra.algebraMap_self_apply, v] using hlz
  refine ⟨V, l, hV0, hC l hl, hVH, hVI, ?_⟩
  have he := congrArg (algebraMap L F) hlv
  change algebraMap L F (aeval v (linearFormPolynomial l)) = algebraMap L F 0 at he
  simpa only [linearFormPolynomial, map_sum, map_mul, map_zero, aeval_C, aeval_X,
    ← IsScalarTower.algebraMap_apply K L F, IntermediateField.algebraMap_apply,
    V, sourceVectorDerivation_coordinate] using he

end DimensionFourDependence
