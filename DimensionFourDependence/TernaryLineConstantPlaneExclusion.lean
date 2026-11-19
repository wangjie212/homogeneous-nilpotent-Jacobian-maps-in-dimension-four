import DimensionFourDependence.SpecifiedCovectorPairFrame
import DimensionFourDependence.LinearConjugacyDerivationTransport
import DimensionFourDependence.TernaryLineSlopeAlgebraicity
import DimensionFourDependence.NormalizedTernaryJacobianRank

/-! # A constant plane for the direction excludes invariant ternary lines -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2250000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)
local notation "x" => (rationalCoordinate (K := K) (n := 3))

/-- A nonzero invariant direction contained in a constant plane for
its direction vector forces dependence of normalized nilpotent outputs. -/
theorem invariant_ternary_line_in_constant_direction_plane_componentsDependent
    (H : Fin 3 → R₃) (h0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (H i) = 0)
    (hN : IsNilpotent (jac H)) (D : Derivation K F F) (hD : D ≠ 0)
    (hH : ∀ i, D (ι (H i)) = 0) (hI : ∀ i, D (D (x i)) = 0)
    (l : Fin 3 → K) (hl : l ≠ 0) (hlD : ∑ i, algebraMap K F (l i) * D (x i) = 0) :
    ComponentsDependent H := by
  by_contra hind
  have hNonzero : ∃ j : Fin 3, D (x j) ≠ 0 := by
    by_contra h
    push Not at h
    apply hD
    exact derivation_ext_rational D 0 h
  obtain ⟨j, hj⟩ := hNonzero
  let r : Fin 3 → K := Pi.single j 1
  let f : (Fin 3 → K) →ₗ[K] F :=
    { toFun := fun c => ∑ i, algebraMap K F (c i) * D (x i)
      map_add' := by
        intro a b
        simp [map_add, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a b
        simp [Algebra.smul_def, map_mul, mul_assoc, Finset.mul_sum] }
  have hf (c : Fin 3 → K) : f c = ∑ i, algebraMap K F (c i) * D (x i) := rfl
  have hfr : f r = D (x j) := by
    classical
    rw [hf, Finset.sum_eq_single j]
    · simp [r]
    · intro i _ hi
      simp [r, hi]
    · simp
  have hfl : f l = 0 := hlD
  have hlin : LinearIndependent K (![l, r] : Fin 2 → (Fin 3 → K)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha
    have he : a 0 • l + a 1 • r = 0 := by simpa only [Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one] using ha
    have h := congrArg f he
    change f (a 0 • l + a 1 • r) = f 0 at h
    have hz : algebraMap K F (a 1) * D (x j) = 0 := by
      rw [map_add, f.map_smul, f.map_smul, map_zero, hfl, hfr, smul_zero, zero_add] at h
      simpa only [Algebra.smul_def] using h
    have ha₁ : a 1 = 0 := (algebraMap K F).injective
      ((mul_eq_zero.mp hz).resolve_right hj |>.trans (map_zero _).symm)
    have h₀ : a 0 • l = 0 := by simpa only [ha₁, zero_smul, add_zero] using he
    have ha₀ := (smul_eq_zero.mp h₀).resolve_right hl
    intro i
    fin_cases i
    · exact ha₀
    · exact ha₁
  let p : Fin 2 ↪ Fin 3 := Fin.succAboveEmb 1
  obtain ⟨T, S, hTS, hST, hRows⟩ := independent_covector_pair_constructs_specified_rows ![l,r] hlin p
  have hS₀ (i : Fin 3) : S 0 i = l i := hRows 0 i
  have hS₂ (i : Fin 3) : S 2 i = r i := hRows 1 i
  let e := matrixSourceFractionEquiv T S hTS hST
  let A := transportDerivation e D
  let G := linearPolynomialConjugate T S H
  have hGn := linearPolynomialConjugate_nilpotent T S hTS hST H hN
  have hGi := linearPolynomialConjugate_componentsIndependent T S hTS hST H hind
  have hG0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (G i) = 0 := by
    have he := linearPolynomialConjugate_aeval_extension_eq_zero T S hTS H
      (fun _ : Fin 3 => (0 : K)) h0
    have hz : S.map (algebraMap K K) *ᵥ (fun _ : Fin 3 => (0 : K)) = 0 := mulVec_zero _
    rw [hz] at he
    exact he
  have hR := closed_field_normalized_independent_ternary_nilpotent_rank_two G hG0 hGi hGn
  have hA (i : Fin 3) : A (x i) = ∑ k, algebraMap K F (S i k) * e (D (x k)) :=
    transportDerivation_matrixSourceFractionEquiv_coordinate T S hTS hST D i
  have hAx : A (x 0) = 0 := by
    rw [hA]
    have he := congrArg e hlD
    change e (∑ i, algebraMap K F (l i) * D (x i)) = e 0 at he
    simpa only [hS₀, map_sum, map_mul, AlgEquiv.commutes, map_zero] using he
  have hAz : A (x 2) ≠ 0 := by
    have he : A (x 2) = e (D (x j)) := by
      classical
      rw [hA, Finset.sum_eq_single j]
      · simp [hS₂, r]
      · intro i _ hi
        simp [hS₂, r, hi]
      · simp
    rw [he]
    exact (map_ne_zero e).mpr hj
  have hAI (i : Fin 3) : A (A (x i)) = 0 :=
    transported_invariant_derivation_direction_is_invariant T S hTS hST D hI i
  have hAG (i : Fin 3) : A (ι (G i)) = 0 :=
    transported_derivation_kills_linearPolynomialConjugate T S hTS hST D H hH i
  let s := (A (x 2))⁻¹ * A (x 1)
  have hS (i : Fin 3) : ternaryLineSlopeDerivation s (x i) = (![0,s,1] : Fin 3 → F) i := by
    fin_cases i <;> simp [ternaryLineSlopeDerivation, Derivation.smul_apply, rationalPartial_coordinate]
  have hScale : ternaryLineSlopeDerivation s = (A (x 2))⁻¹ • A := by
    apply derivation_ext_rational
    intro i
    rw [hS, Derivation.smul_apply, smul_eq_mul]
    fin_cases i
    · change 0 = (A (x 2))⁻¹ * A (x 0)
      rw [hAx, mul_zero]
    · rfl
    · change 1 = (A (x 2))⁻¹ * A (x 2)
      rw [inv_mul_cancel₀ hAz]
  have hSS : ternaryLineSlopeDerivation s s = 0 := by
    rw [hScale, Derivation.smul_apply, smul_eq_mul]
    change (A (x 2))⁻¹ * A ((A (x 2))⁻¹ * A (x 1)) = 0
    rw [A.leibniz, A.leibniz_inv, hAI 2, hAI 1]
    simp
  have hSG (i : Fin 3) : ternaryLineSlopeDerivation s (ι (G i)) = 0 := by
    rw [hScale, Derivation.smul_apply, hAG, smul_zero]
  exact hGi (invariant_ternary_line_with_fixed_first_coordinate_componentsDependent G hG0 hGn hR s hSG hSS)

end DimensionFourDependence
