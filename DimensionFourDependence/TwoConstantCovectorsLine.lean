import DimensionFourDependence.ConstantPlaneProjection
import DimensionFourDependence.RulingFormCoordinateSpan
import DimensionFourDependence.AffineLineDerivation

/-! # Two independent constant covectors cut an actual affine line

The two specified covectors construct a right inverse and a one-dimensional
kernel over the original field. The original kernel coordinate identity
remains valid after coefficient extension, giving the actual affine-line
expression for every extension-valued point with the specified constant values.
-/

namespace DimensionFourDependence

open Matrix Module

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

/-- A point in three coordinates with two independent original-field
linear forms taking original-field values lies on an actual original-field affine line. -/
theorem two_constant_covectors_liesInAffineLine
    (a b : Fin 3 → L) (hab : LinearIndependent L ![a, b])
    (x : Fin 3 → F) (r s : L)
    (ha : (fun i => algebraMap L F (a i)) ⬝ᵥ x = algebraMap L F r)
    (hb : (fun i => algebraMap L F (b i)) ⬝ᵥ x = algebraMap L F s) :
    LiesInAffineLine (E := L) x := by
  classical
  let B : Matrix (Fin 3) (Fin 2) L := fun i j => ![a, b] j i
  have hC : ∃ C : Matrix (Fin 2) (Fin 3) L, C * B = 1 := by
    rcases linear_dichotomy B with ⟨c, hc, hzero⟩ | hC
    · exfalso
      apply hc
      have he : ∑ j : Fin 2, c j • ![a, b] j = 0 := by
        funext i
        have hi := congrFun hzero i
        simpa only [Matrix.mulVec, dotProduct, B, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, mul_comm, Pi.zero_apply] using hi
      exact funext (Fintype.linearIndependent_iff.mp hab c he)
    · exact hC
  obtain ⟨C, hCB⟩ := hC
  let A := B.transpose
  let D := C.transpose
  have hAD : A * D = 1 := by
    change B.transpose * C.transpose = 1
    rw [← Matrix.transpose_mul, hCB, Matrix.transpose_one]
  have hsurj : Function.Surjective A.toLin' := by
    intro y
    refine ⟨D *ᵥ y, ?_⟩
    change A *ᵥ (D *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, hAD, Matrix.one_mulVec]
  have hdim : finrank L (LinearMap.ker A.toLin') = 1 := by
    have he := LinearMap.finrank_range_add_finrank_ker A.toLin'
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at he
    norm_num at he
    omega
  obtain ⟨v, hv0, hvspan⟩ := finrank_eq_one_iff'.mp hdim
  have hv : (v : Fin 3 → L) ≠ 0 := fun he => hv0 (Subtype.ext he)
  obtain ⟨k, hk⟩ : ∃ k, (v : Fin 3 → L) k ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hv
  let ell : Fin 3 → L := Pi.single k ((v : Fin 3 → L) k)⁻¹
  have hell : ell ⬝ᵥ (v : Fin 3 → L) = 1 := by
    rw [show ell = Pi.single k ((v : Fin 3 → L) k)⁻¹ from rfl, single_dotProduct, inv_mul_cancel₀ hk]
  have hspan : ∀ z ∈ LinearMap.ker A.toLin', ∀ i,
      z i = (v : Fin 3 → L) i * (ell ⬝ᵥ z) + (0 : Fin 3 → L) i * ((0 : Fin 3 → L) ⬝ᵥ z) := by
    intro z hz i
    obtain ⟨c, hc⟩ := hvspan ⟨z, hz⟩
    have hzv : z = c • (v : Fin 3 → L) := (congrArg Subtype.val hc).symm
    rw [hzv, dotProduct_smul, hell]
    simp only [Pi.smul_apply, smul_eq_mul, mul_one, Pi.zero_apply, zero_mul, add_zero, mul_comm]
  let x0 : Fin 3 → L := D *ᵥ ![r, s]
  have hAx0 : A *ᵥ x0 = ![r, s] := by
    change A *ᵥ (D *ᵥ ![r, s]) = _
    rw [Matrix.mulVec_mulVec, hAD, Matrix.one_mulVec]
  have hAx : A.map (algebraMap L F) *ᵥ x = fun i => algebraMap L F (![r, s] i) := by
    funext i
    fin_cases i
    · change (fun i => algebraMap L F (a i)) ⬝ᵥ x = algebraMap L F r
      exact ha
    · change (fun i => algebraMap L F (b i)) ⬝ᵥ x = algebraMap L F s
      exact hb
  let z : Fin 3 → F := x - fun i => algebraMap L F (x0 i)
  have hAz : A.map (algebraMap L F) *ᵥ z = 0 := by
    change A.map (algebraMap L F) *ᵥ (x - fun i => algebraMap L F (x0 i)) = 0
    rw [Matrix.mulVec_sub, hAx]
    have he : A.map (algebraMap L F) *ᵥ (fun i => algebraMap L F (x0 i)) =
        fun i => algebraMap L F ((A *ᵥ x0) i) := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
    rw [he, hAx0, sub_self]
  have hz := matrix_kernel_coordinate_form_span_after_extension A ell (0 : Fin 3 → L)
    (v : Fin 3 → L) (0 : Fin 3 → L) hspan z hAz
  refine ⟨x0, v, hv, (fun i => algebraMap L F (ell i)) ⬝ᵥ z, ?_⟩
  intro i
  have hi := hz i
  simp only [Pi.zero_apply, map_zero, zero_mul, add_zero] at hi
  change x i - algebraMap L F (x0 i) = _ at hi
  linear_combination hi

end DimensionFourDependence
