/- Adapted from the neighboring quartic project's Rank2/Gradient.lean.
   These rational derivative constructions are independent of its main theorem.
   The original attribution is retained in the docstrings. -/
import DimensionFourDependence.Defs

/-!
# Partial derivatives of rational functions

Auxiliary material for the rank-two part of Lemma 2.1 of `quartic_dependence.pdf`
("By the Jacobian criterion, `rank JF` is the transcendence degree of `K(F)`").  We extend
the partial derivatives `∂/∂xₗ` from `K[x]` to the field of rational functions `K(x)` (via
the dual numbers), and record the chain rule for elements of an intermediate field.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {σ : Type*}

/-- The ring homomorphism `P ↦ P + ε ∂P/∂xₗ` from `K[x]` to the dual numbers over `K(x)`
(auxiliary for the Jacobian criterion used in Lemma 2.1 of `quartic_dependence.pdf`). -/
noncomputable def dualPolyHom (l : σ) :
    MvPolynomial σ K →+* DualNumber (FractionRing (MvPolynomial σ K)) where
  toFun P := TrivSqZeroExt.inl (algebraMap _ _ P) +
    TrivSqZeroExt.inr (algebraMap _ _ (pderiv l P))
  map_one' := by simp
  map_mul' P Q := by
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
        zero_add, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero, Derivation.leibniz, map_add, map_mul, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring
  map_zero' := by simp
  map_add' P Q := by
    ext
    · simp
    · simp only [map_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
        zero_add]

/-- Nonzero polynomials map to units of the dual numbers under `P ↦ P + ε ∂P/∂xₗ`. (Auxiliary for
the proof of Lemma 2.1 of `quartic_dependence.pdf`.) -/
theorem isUnit_dualPolyHom (l : σ) (y : nonZeroDivisors (MvPolynomial σ K)) :
    IsUnit (dualPolyHom (K := K) l y) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simp only [dualPolyHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
    isUnit_iff_ne_zero, ne_eq]
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2

/-- The extension of `P ↦ P + ε ∂P/∂xₗ` to the field of rational functions. (Auxiliary for the
proof of Lemma 2.1 of `quartic_dependence.pdf`.) -/
noncomputable def fracDerivHom (l : σ) :
    FractionRing (MvPolynomial σ K) →+* DualNumber (FractionRing (MvPolynomial σ K)) :=
  IsLocalization.lift (M := nonZeroDivisors (MvPolynomial σ K)) (isUnit_dualPolyHom l)

/-- The partial derivative `∂/∂xₗ` on the field of rational functions `K(x)`. (Auxiliary for the
proof of Lemma 2.1 of `quartic_dependence.pdf`.) -/
noncomputable def fracDeriv (l : σ) (f : FractionRing (MvPolynomial σ K)) :
    FractionRing (MvPolynomial σ K) :=
  (fracDerivHom l f).snd

/-- On polynomials, `fracDerivHom` is `P ↦ P + ε ∂P/∂xₗ`. (Auxiliary for the proof of Lemma 2.1 of
`quartic_dependence.pdf`.) -/
theorem fracDerivHom_algebraMap (l : σ) (P : MvPolynomial σ K) :
    fracDerivHom l (algebraMap _ (FractionRing (MvPolynomial σ K)) P) = dualPolyHom l P :=
  IsLocalization.lift_eq _ _

/-- The first component of `fracDerivHom l f` is `f`. (Auxiliary for the proof of Lemma 2.1 of
`quartic_dependence.pdf`.) -/
theorem fst_fracDerivHom (l : σ) (f : FractionRing (MvPolynomial σ K)) :
    (fracDerivHom l f).fst = f := by
  have : (TrivSqZeroExt.fstHom (FractionRing (MvPolynomial σ K))
      (FractionRing (MvPolynomial σ K)) (FractionRing (MvPolynomial σ K))).toRingHom.comp
      (fracDerivHom l) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial σ K))
    refine RingHom.ext fun P => ?_
    simp only [RingHom.comp_apply, fracDerivHom_algebraMap, RingHom.id_apply]
    simp [dualPolyHom]
  exact congrArg (fun φ : FractionRing (MvPolynomial σ K) →+* _ => φ f) this

/-- The partial derivative on `K(x)` extends `pderiv` on `K[x]`. (Auxiliary for the proof of Lemma
2.1 of `quartic_dependence.pdf`.) -/
theorem fracDeriv_algebraMap (l : σ) (P : MvPolynomial σ K) :
    fracDeriv l (algebraMap _ (FractionRing (MvPolynomial σ K)) P) =
      algebraMap _ _ (pderiv l P) := by
  simp only [fracDeriv, fracDerivHom_algebraMap, dualPolyHom, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
    zero_add]

/-- Additivity of the partial derivative on `K(x)`. (Auxiliary for the proof of Lemma 2.1 of
`quartic_dependence.pdf`.) -/
theorem fracDeriv_add (l : σ) (f g : FractionRing (MvPolynomial σ K)) :
    fracDeriv l (f + g) = fracDeriv l f + fracDeriv l g := by
  simp [fracDeriv]

/-- Leibniz rule for the partial derivative on `K(x)`. (Auxiliary for the proof of Lemma 2.1 of
`quartic_dependence.pdf`.) -/
theorem fracDeriv_mul (l : σ) (f g : FractionRing (MvPolynomial σ K)) :
    fracDeriv l (f * g) = f * fracDeriv l g + g * fracDeriv l f := by
  simp only [fracDeriv, map_mul, TrivSqZeroExt.snd_mul, fst_fracDerivHom, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

/-- The partial derivative on `K(x)` commutes with negation. (Auxiliary for the proof of Lemma 2.1
of `quartic_dependence.pdf`.) -/
theorem fracDeriv_neg (l : σ) (f : FractionRing (MvPolynomial σ K)) :
    fracDeriv l (-f) = -fracDeriv l f := by
  simp [fracDeriv]

/-- Constants have zero partial derivatives. (Auxiliary for the proof of Lemma 2.1 of
`quartic_dependence.pdf`.) -/
theorem fracDeriv_algebraMap_field (l : σ) (c : K) :
    fracDeriv l (algebraMap K (FractionRing (MvPolynomial σ K)) c) = 0 := by
  rw [IsScalarTower.algebraMap_apply K (MvPolynomial σ K), fracDeriv_algebraMap,
    algebraMap_eq, pderiv_C, map_zero]

/-- The partial derivative of `1` is zero. (Auxiliary for the proof of Lemma 2.1 of
`quartic_dependence.pdf`.) -/
theorem fracDeriv_one (l : σ) : fracDeriv l (1 : FractionRing (MvPolynomial σ K)) = 0 := by
  simpa using fracDeriv_algebraMap_field (K := K) l 1

/-- Quotient rule: `∂(f⁻¹) = −f⁻² ∂f`. (Auxiliary for the proof of Lemma 2.1 of
`quartic_dependence.pdf`.) -/
theorem fracDeriv_inv (l : σ) (f : FractionRing (MvPolynomial σ K)) :
    fracDeriv l f⁻¹ = -(f⁻¹ ^ 2 * fracDeriv l f) := by
  by_cases hf : f = 0
  · subst hf; simp [fracDeriv]
  have h := fracDeriv_mul l f f⁻¹
  rw [mul_inv_cancel₀ hf, fracDeriv_one] at h
  have e : fracDeriv l f⁻¹ = f⁻¹ * (f * fracDeriv l f⁻¹) := by
    rw [← mul_assoc, inv_mul_cancel₀ hf, one_mul]
  rw [e, show f * fracDeriv l f⁻¹ = -(f⁻¹ * fracDeriv l f) by linear_combination -h]
  ring

/-- Power rule: `∂(fᵏ⁺¹) = (k + 1) fᵏ ∂f`. (Auxiliary for the proof of Lemma 2.1 of
`quartic_dependence.pdf`.) -/
theorem fracDeriv_pow (l : σ) (f : FractionRing (MvPolynomial σ K)) (k : ℕ) :
    fracDeriv l (f ^ (k + 1)) = (k + 1 : FractionRing (MvPolynomial σ K)) * f ^ k *
      fracDeriv l f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, fracDeriv_mul, ih]
    push_cast
    ring

/-- The gradient `∇f = (∂f/∂x₁, …, ∂f/∂xₙ)` of a rational function. (Auxiliary for the proof of
Lemma 2.1 of `quartic_dependence.pdf`.) -/
noncomputable def fracGrad {n : ℕ} (f : FractionRing (MvPolynomial (Fin n) K)) :
    Fin n → FractionRing (MvPolynomial (Fin n) K) :=
  fun l => fracDeriv l f

/-- Additivity of the gradient on `K(x)`. (Auxiliary for the proof of Lemma 2.1 of
`quartic_dependence.pdf`.) -/
theorem fracGrad_add {n : ℕ} (f g : FractionRing (MvPolynomial (Fin n) K)) :
    fracGrad (f + g) = fracGrad f + fracGrad g := by
  funext l; simp [fracGrad, fracDeriv_add]

/-- Leibniz rule for the gradient on `K(x)`. (Auxiliary for the proof of Lemma 2.1 of
`quartic_dependence.pdf`.) -/
theorem fracGrad_mul {n : ℕ} (f g : FractionRing (MvPolynomial (Fin n) K)) :
    fracGrad (f * g) = f • fracGrad g + g • fracGrad f := by
  funext l; simp [fracGrad, fracDeriv_mul]

/-- Quotient rule for the gradient on `K(x)`. (Auxiliary for the proof of Lemma 2.1 of
`quartic_dependence.pdf`.) -/
theorem fracGrad_inv {n : ℕ} (f : FractionRing (MvPolynomial (Fin n) K)) :
    fracGrad f⁻¹ = (-(f⁻¹ ^ 2)) • fracGrad f := by
  funext l; simp [fracGrad, fracDeriv_inv]

/-- Constants have zero gradient. (Auxiliary for the proof of Lemma 2.1 of
`quartic_dependence.pdf`.) -/
theorem fracGrad_algebraMap_field {n : ℕ} (c : K) :
    fracGrad (algebraMap K (FractionRing (MvPolynomial (Fin n) K)) c) = 0 := by
  funext l; simp [fracGrad, fracDeriv_algebraMap_field]

/-- The gradient of a polynomial is the vector of its partial derivatives. (Auxiliary for the
proof of Lemma 2.1 of `quartic_dependence.pdf`.) -/
theorem fracGrad_algebraMap {n : ℕ} (P : MvPolynomial (Fin n) K) :
    fracGrad (algebraMap _ (FractionRing (MvPolynomial (Fin n) K)) P) =
      fun l => algebraMap _ _ (pderiv l P) := by
  funext l; simp [fracGrad, fracDeriv_algebraMap]

/-- The gradient of the coordinate `xⱼ` is the `j`-th standard basis vector. (Auxiliary for the
proof of Lemma 2.1 of `quartic_dependence.pdf`.) -/
theorem fracGrad_X {n : ℕ} (j : Fin n) :
    fracGrad (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (X j)) =
      Pi.single j 1 := by
  rw [fracGrad_algebraMap]
  funext l
  by_cases h : l = j
  · subst h; simp
  · simp [pderiv_X, Pi.single_apply, h, Ne.symm h]

/-- Chain rule for an intermediate field: the gradient of any element of the field generated
by a set `u` lies in the `K(x)`-span of the gradients of the elements of `u`. (Auxiliary for the
proof of Lemma 2.1 of `quartic_dependence.pdf`.) -/
theorem fracGrad_mem_span_of_mem_adjoin {n : ℕ}
    {u : Set (FractionRing (MvPolynomial (Fin n) K))}
    {f : FractionRing (MvPolynomial (Fin n) K)} (hf : f ∈ IntermediateField.adjoin K u) :
    fracGrad f ∈ Submodule.span (FractionRing (MvPolynomial (Fin n) K)) (fracGrad '' u) := by
  induction hf using IntermediateField.adjoin_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | algebraMap x => rw [fracGrad_algebraMap_field]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [fracGrad_add]; exact Submodule.add_mem _ hx hy
  | inv x _ hx => rw [fracGrad_inv]; exact Submodule.smul_mem _ _ hx
  | mul x y _ _ hx hy =>
    rw [fracGrad_mul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx)

end DimensionFourDependence
