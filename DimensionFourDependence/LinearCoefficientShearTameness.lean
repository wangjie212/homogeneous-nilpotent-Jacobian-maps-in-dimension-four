import DimensionFourDependence.CoprimeLinearShearCoordinates
import DimensionFourDependence.LinearBaseShearFrame
import DimensionFourDependence.ConstructiveDeterminantShearTameness
import DimensionFourDependence.ShearAutomorphism

/-! # Coprime linear coefficient shears are conjugate to Lemma 6.2 -/

namespace DimensionFourDependence.Shear

open Matrix MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "M₂" => Matrix (Fin 2) (Fin 2) K

/-- Rewrite the two original coefficient variables in the independent
linear coefficient coordinates, retaining the invariant as first variable. -/
noncomputable def linearBaseShearParameter3 (T : M₂) (f : R₃) : R₃ :=
  aeval ![X 0, rename Fin.succ (linearPolynomialMap T⁻¹ 0),
    rename Fin.succ (linearPolynomialMap T⁻¹ 1)] f

theorem determinant_parameter_rename_base
    (p : MvPolynomial (Fin 2) K) :
    (aeval (![DeterminantShear.invariant4, X 2, X 3] : Fin 3 → R₄)) (rename Fin.succ p) = base4 p := by
  have h : (aeval (![DeterminantShear.invariant4, X 2, X 3] : Fin 3 → R₄)).comp
      (rename (R := K) (Fin.succ : Fin 2 → Fin 3)) = aeval ![X 2, X 3] := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j <;> simp
  exact AlgHom.congr_fun h p

theorem signBaseFrameEquiv4_determinant (T : M₂) (h : IsUnit T.det) :
    signBaseFrameEquiv4 T h (DeterminantShear.invariant4 : R₄) =
      invariant4 (linearPolynomialMap T 0) (linearPolynomialMap T 1) := by
  simp [DeterminantShear.invariant4, invariant4, signBaseFrameEquiv4_X]

/-- The entire original parameter is recovered after the coefficient
change. This is an identity of actual polynomials for arbitrary `f`. -/
theorem signBaseFrameEquiv4_determinant_parameter
    (T : M₂) (h : IsUnit T.det) (f : R₃) :
    signBaseFrameEquiv4 T h (DeterminantShear.parameter4 (linearBaseShearParameter3 T f)) =
      parameter4 (linearPolynomialMap T 0) (linearPolynomialMap T 1) f := by
  unfold DeterminantShear.parameter4 linearBaseShearParameter3
  rw [comp_aeval_apply]
  change (signBaseFrameEquiv4 T h).toAlgHom (aeval _ f) = _
  rw [Tame.algHom_aeval]
  have hb (i : Fin 2) :
      signBaseFrameEquiv4 T h (base4 (linearPolynomialMap T⁻¹ i)) =
        (![X 2, X 3] : Fin 2 → R₄) i := by
    rw [signBaseFrameEquiv4_base]
    have hi := matrix_linear_polynomial_substitution_inverse T⁻¹ T (Matrix.nonsing_inv_mul T h) (X i)
    simp only [linearPolynomialPullback, aeval_X] at hi
    rw [show linearPolynomialPullback T (linearPolynomialMap T⁻¹ i) = X i from hi, base4]
    exact aeval_X _ _
  have hg : (fun j : Fin 3 => signBaseFrameEquiv4 T h
      ((aeval (![DeterminantShear.invariant4, X 2, X 3] : Fin 3 → R₄))
        ((![X 0, rename Fin.succ (linearPolynomialMap T⁻¹ 0),
          rename Fin.succ (linearPolynomialMap T⁻¹ 1)] : Fin 3 → R₃) j))) =
      ![invariant4 (linearPolynomialMap T 0) (linearPolynomialMap T 1), X 2, X 3] := by
    funext j
    fin_cases j
    · simp [signBaseFrameEquiv4_determinant]
    · change signBaseFrameEquiv4 T h
        (aeval (![DeterminantShear.invariant4, X 2, X 3] : Fin 3 → R₄)
          (rename Fin.succ (linearPolynomialMap T⁻¹ 0))) = X 2
      rw [determinant_parameter_rename_base, hb]
      rfl
    · change signBaseFrameEquiv4 T h
        (aeval (![DeterminantShear.invariant4, X 2, X 3] : Fin 3 → R₄)
          (rename Fin.succ (linearPolynomialMap T⁻¹ 1))) = X 3
      rw [determinant_parameter_rename_base, hb]
      rfl
  simpa only [parameter4, AlgEquiv.coe_toAlgHom] using
    congrArg (fun v : Fin 3 → R₄ => aeval v f) hg

/-- The actual original shear is the conjugate of the determinant shear.
The negative sign of the second active coordinate gives the correct
sign in both the invariant and the perturbation. -/
theorem automorphism4_linear_base_conjugacy (T : M₂) (h : IsUnit T.det) (f : R₃) :
    automorphism4 (linearPolynomialMap T 0) (linearPolynomialMap T 1) f =
      signBaseFrameEquiv4 T h * DeterminantShear.automorphism4 (linearBaseShearParameter3 T f) *
        (signBaseFrameEquiv4 T h)⁻¹ := by
  let a := linearPolynomialMap T 0
  let b := linearPolynomialMap T 1
  let E := signBaseFrameEquiv4 T h
  let D := DeterminantShear.automorphism4 (linearBaseShearParameter3 T f)
  let F := automorphism4 a b f
  have hp : E (DeterminantShear.parameter4 (linearBaseShearParameter3 T f)) = parameter4 a b f :=
    signBaseFrameEquiv4_determinant_parameter T h f
  have hE (j : Fin 4) : E (X j) = ![X 0, -X 1, base4 a, base4 b] j := signBaseFrameEquiv4_X T h j
  have hD (j : Fin 4) : D (X j) =
      ![X 0 + X 3 * DeterminantShear.parameter4 (linearBaseShearParameter3 T f),
        X 1 + X 2 * DeterminantShear.parameter4 (linearBaseShearParameter3 T f), X 2, X 3] j :=
    DeterminantShear.automorphism4_X _ j
  have hF (j : Fin 4) : F (X j) = X j + perturbation4 a b f j := automorphism4_X a b f j
  have hbase (p : MvPolynomial (Fin 2) K) : F (base4 p) = base4 p :=
    substitution4_base a b p f
  have he : F * E = E * D := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply MvPolynomial.algHom_ext
    intro j
    change F (E (X j)) = E (D (X j))
    rw [hE, hD]
    fin_cases j <;> simp [hF, hE, hp, hbase, perturbation4, add_comm]
  change F = E * D * E⁻¹
  rw [← he, mul_inv_cancel_right]

variable [CharZero K]

/-- A relatively prime homogeneous linear pair gives an actual tame
four-variable shear by Lemma 6.2 over the original coefficient field. -/
theorem automorphism4_coprime_linear_coefficients_tame
    (a b : MvPolynomial (Fin 2) K) (ha : a.IsHomogeneous 1) (hb : b.IsHomogeneous 1)
    (hc : IsRelPrime a b) (f : R₃) : automorphism4 a b f ∈ Tame.subgroup K 4 := by
  obtain ⟨T, hT, hea, heb⟩ := coprime_homogeneous_linear_coefficients_construct_frame a b ha hb hc
  rw [hea, heb, automorphism4_linear_base_conjugacy T hT]
  have ht : signBaseFrameEquiv4 T hT ∈ Tame.subgroup K 4 :=
    Subgroup.subset_closure (Or.inl (signBaseFrameEquiv4_isAffine T hT))
  exact (Tame.subgroup K 4).mul_mem
    ((Tame.subgroup K 4).mul_mem ht (DeterminantShear.automorphism4_tame _))
    ((Tame.subgroup K 4).inv_mem ht)

end DimensionFourDependence.Shear
