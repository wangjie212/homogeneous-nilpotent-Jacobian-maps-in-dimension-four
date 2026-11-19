import DimensionFourDependence.FixedVertexCharacteristicAxis
import DimensionFourDependence.ScaledPlaneNormalizedBaseBranch

/-! # The fixed vertex constructs the independent ruling output coordinates -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module AlgebraicGeometry

set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000

/-- A scalar-extended point of a matrix kernel satisfies every
original covector that vanishes on that whole original kernel. -/
theorem matrix_kernel_zero_restriction_pairing_after_extension
    {E F : Type*} [Field E] [Field F] [Algebra E F] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) E) (c : Fin n → E)
    (hc : rulingFormRestriction (LinearMap.ker A.toLin') c = 0)
    (y : Fin n → F) (hy : A.map (algebraMap E F) *ᵥ y = 0) :
    (fun i => algebraMap E F (c i)) ⬝ᵥ y = 0 := by
  let B : Matrix (Fin 1) (Fin n) E := fun _ i => c i
  have hker : LinearMap.ker A.toLin' ≤ LinearMap.ker B.toLin' := by
    intro x hx
    change B *ᵥ x = 0
    funext r
    have he := LinearMap.congr_fun hc ⟨x, hx⟩
    change c ⬝ᵥ x = 0 at he
    exact he
  have he := matrix_kernel_le_after_scalar_extension (E := F) A B hker
    (show y ∈ LinearMap.ker (A.map (algebraMap E F)).toLin' from hy)
  exact congrFun he 0

/-- Two covectors are independent when one is nonzero at a
specified vector and the other vanishes there but is not the zero form. -/
theorem dual_pair_independent_of_separating_vector
    {E M : Type*} [Field E] [AddCommGroup M] [Module E M]
    (s n : Module.Dual E M) (v : M) (hs : s v ≠ 0) (hn : n ≠ 0) (hnv : n v = 0) :
    LinearIndependent E ![s, n] := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hv := LinearMap.congr_fun hc v
  have hc0 : c 0 = 0 := by
    have he : c 0 * s v = 0 := by
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, LinearMap.zero_apply, hnv, mul_zero, add_zero] using hv
    exact (mul_eq_zero.mp he).resolve_right hs
  have hnsmul : c 1 • n = 0 := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, hc0, zero_smul, zero_add] using hc
  have hc1 : c 1 = 0 := (smul_eq_zero.mp hnsmul).resolve_right hn
  fin_cases i
  · exact hc0
  · exact hc1

universe u

set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "W₀" => LinearMap.ker (A₀).toLin'
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E

local instance fixedVertexScaledOutputSpanIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance fixedVertexScaledOutputSpanAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

include hvertex

/-- The actual output numerator's nonvanishing makes its original
restriction to the chosen ruling a nonzero form. -/
theorem actual_nonzero_output_covector_restriction_ne_zero
    (n : Fin 4 → E) (hn : aeval (w) ((O) n) ≠ 0) :
    rulingFormRestriction W₀ n ≠ 0 := by
  intro hz
  have hp := matrix_kernel_zero_restriction_pairing_after_extension (A₀) n hz
    (fun i => aeval (w) (MvPolynomial.map (ι) (H i)))
    (extendedClosedGauss_native_output_mem_chosen_ruling H I E hH e hd hind hGauss)
  apply hn
  simpa only [extendedClosedGaussOutputLinearPolynomial, MvPolynomial.smul_eq_C_mul,
    map_sum, map_mul, aeval_C, dotProduct] using hp

/-- The actual specified vertex and nonzero numerator construct
the two independent ruling restrictions and all original output-span
coefficients. Neither restriction independence nor component spans are input. -/
theorem fixed_vertex_scaled_output_covectors_construct_original_output_span
    (s n : Fin 4 → E) (hs : s (Fin.last 3) ≠ 0)
    (hnlast : n (Fin.last 3) = 0) (hn : aeval (w) ((O) n) ≠ 0) :
    LinearIndependent E ![rulingFormRestriction W₀ s, rulingFormRestriction W₀ n] ∧
      ∃ bS bN : Fin 4 → E, ∀ i,
        aeval (w) (MvPolynomial.map (ι) (H i)) =
          algebraMap E (N).functionField (bS i) * aeval (w) ((O) s) +
            algebraMap E (N).functionField (bN i) * aeval (w) ((O) n) := by
  let v : Fin 4 → E := Fin.snoc (0 : Fin 3 → E) 1
  have hv : v ∈ W₀ := by
    change (A₀) *ᵥ v = 0
    funext r
    change (∑ i, (A₀) r i * v i) = 0
    rw [Fin.sum_univ_castSucc]
    simp only [v, Fin.snoc_castSucc, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      Fin.snoc_last, mul_one, zero_add]
    exact extended_chosen_ruling_fixed_vertex_last_column H I E hH hd hind hGauss hvertex r
  have heval (c : Fin 4 → E) : rulingFormRestriction W₀ c ⟨v, hv⟩ = c (Fin.last 3) := by
    change (∑ i, c i * v i) = _
    rw [Fin.sum_univ_castSucc]
    simp only [v, Fin.snoc_castSucc, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      Fin.snoc_last, mul_one, zero_add]
  have hpair := dual_pair_independent_of_separating_vector
    (rulingFormRestriction W₀ s) (rulingFormRestriction W₀ n) ⟨v, hv⟩
    (by rw [heval]; exact hs)
    (actual_nonzero_output_covector_restriction_ne_zero H I E hH e hd hind hGauss hvertex n hn)
    (by rw [heval]; exact hnlast)
  exact ⟨hpair, extendedClosedGauss_native_output_span_of_chosen_ruling_forms
    H I E hH e hd hind hGauss s n hpair⟩

end DimensionFourDependence
