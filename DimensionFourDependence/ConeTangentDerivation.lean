import DimensionFourDependence.ConeParameterDifferential

/-! # Every cone tangent vector is realized by a field derivation

The original polynomial differential defines a dual-number point.
Tangency kills the cone equation, and the exact cone prime extends the
point to the actual residue field. Its infinitesimal part is the required
derivation, with the prescribed values on all original coordinates.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] {n : ℕ}
  (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

local notation "S" => MvPolynomial (Fin n) K
local notation "κ" => Q.ResidueField

/-- The original tangent direction defines an actual polynomial
point over the dual numbers of the original cone field. -/
noncomputable def coneTangentDualPolynomialHom (v : Fin n → κ) : S →ₐ[K] DualNumber κ where
  toFun p := TrivSqZeroExt.inl (algebraMap S κ p) +
    TrivSqZeroExt.inr (mappedPolynomialGradient (algebraMap S κ) p ⬝ᵥ v)
  map_one' := by
    ext <;> simp [mappedPolynomialGradient, dotProduct]
  map_zero' := by
    ext <;> simp [mappedPolynomialGradient, dotProduct]
  map_add' p q := by
    ext <;> simp [mappedPolynomialGradient, dotProduct, add_mul, Finset.sum_add_distrib]
  map_mul' p q := by
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
        zero_add, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op, mappedPolynomialGradient_product_pairing]
      ring
  commutes' c := by
    ext
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
      change algebraMap S κ (algebraMap K S c) =
        (algebraMap K (DualNumber κ) c).fst
      rw [← IsScalarTower.algebraMap_apply K S κ,
        TrivSqZeroExt.algebraMap_eq_inl']
      rfl
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      change mappedPolynomialGradient (algebraMap S κ) (C c) ⬝ᵥ v =
        (algebraMap K (DualNumber κ) c).snd
      rw [TrivSqZeroExt.algebraMap_eq_inl']
      simp [mappedPolynomialGradient, dotProduct]

theorem coneTangentDualPolynomialHom_fst (v : Fin n → κ) (p : S) :
    (coneTangentDualPolynomialHom Q v p).fst = algebraMap S κ p := by
  simp [coneTangentDualPolynomialHom]

theorem coneTangentDualPolynomialHom_snd (v : Fin n → κ) (p : S) :
    (coneTangentDualPolynomialHom Q v p).snd = mappedPolynomialGradient (algebraMap S κ) p ⬝ᵥ v := by
  simp [coneTangentDualPolynomialHom]

/-- Every vector in the original cone's actual tangent hyperplane
comes from a derivation of its own function field. Neither a lift nor
smoothness nor a coordinate chart is assumed. -/
theorem cone_tangent_vector_constructs_field_derivation
    (R : S) (hQ : Q = Ideal.span {R}) (v : Fin n → κ)
    (hv : mappedPolynomialGradient (algebraMap S κ) R ⬝ᵥ v = 0) :
    ∃ D : Derivation K κ κ, ∀ i, D (algebraMap S κ (X i)) = v i := by
  let g := coneTangentDualPolynomialHom Q v
  have hR : g R = 0 := by
    apply TrivSqZeroExt.ext
    · rw [coneTangentDualPolynomialHom_fst]
      exact source_cone_equation_residue_eq_zero Q R hQ
    · rw [coneTangentDualPolynomialHom_snd, hv]
      rfl
  have hker : Q ≤ RingHom.ker g := by
    calc
      Q = Ideal.span {R} := hQ
      _ ≤ RingHom.ker g := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hR)
  have hunit : Q.primeCompl ≤ (IsUnit.submonoid (DualNumber κ)).comap g := by
    intro p hp
    change IsUnit (g p)
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, coneTangentDualPolynomialHom_fst]
    exact isUnit_iff_ne_zero.mpr (fun hz => hp (Ideal.algebraMap_residueField_eq_zero.mp hz))
  let l : κ →ₐ[K] DualNumber κ := Ideal.ResidueField.liftₐ Q g hker hunit
  have hfst : (TrivSqZeroExt.fstHom K κ κ).comp l = AlgHom.id K κ := by
    apply Ideal.ResidueField.algHom_ext
    apply AlgHom.ext
    intro p
    change (l (algebraMap S κ p)).fst = algebraMap S κ p
    dsimp only [l]
    rw [Ideal.ResidueField.liftₐ_algebraMap, coneTangentDualPolynomialHom_fst]
  have hfst_value (x : κ) : (l x).fst = x := DFunLike.congr_fun hfst x
  let D : Derivation K κ κ :=
    { toLinearMap :=
        { toFun := fun x => (l x).snd
          map_add' := by intro x y; simp
          map_smul' := by intro c x; simp only [map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply] }
      map_one_eq_zero' := by change (l (1 : κ)).snd = 0; rw [map_one]; rfl
      leibniz' := by
        intro x y
        change (l (x * y)).snd = x * (l y).snd + y * (l x).snd
        simp only [map_mul, TrivSqZeroExt.snd_mul, hfst_value, smul_eq_mul,
          MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
        ring }
  refine ⟨D, ?_⟩
  intro i
  change (l (algebraMap S κ (X i))).snd = v i
  dsimp only [l]
  rw [Ideal.ResidueField.liftₐ_algebraMap, coneTangentDualPolynomialHom_snd]
  simp [mappedPolynomialGradient, dotProduct, pderiv_X, Pi.single_apply]

end DimensionFourDependence
