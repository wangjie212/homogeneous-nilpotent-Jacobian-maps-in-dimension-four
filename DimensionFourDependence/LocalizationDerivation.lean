import DimensionFourDependence.Defs

/-! # Derivations extend to the actual source localization -/

namespace DimensionFourDependence

set_option maxHeartbeats 3000000

variable {K R S : Type*} [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra R S] [Algebra K S] [IsScalarTower K R S]
  (M : Submonoid R) [IsLocalization M S]

/-- The first-order source homomorphism `r -> r + epsilon*D(r)`,
with both values realized in the specified localization. -/
noncomputable def localizationDerivationSourceDualHom (D : Derivation K R R) : R →+* DualNumber S where
  toFun r := TrivSqZeroExt.inl (algebraMap R S r) + TrivSqZeroExt.inr (algebraMap R S (D r))
  map_one' := by simp
  map_mul' r t := by
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
        zero_add, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero, Derivation.leibniz, map_add, map_mul, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring
  map_zero' := by simp
  map_add' r t := by
    ext
    · simp
    · simp [map_add, Algebra.smul_def]

/-- Every inverted denominator still maps to a dual-number unit. -/
theorem localizationDerivationSourceDualHom_isUnit (D : Derivation K R R) (m : M) :
    IsUnit (localizationDerivationSourceDualHom (S := S) D m) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa [localizationDerivationSourceDualHom] using IsLocalization.map_units S m

/-- The localized first-order homomorphism constructs the derivative
on every regular fraction. -/
noncomputable def localizationDerivationDualHom (D : Derivation K R R) : S →+* DualNumber S :=
  IsLocalization.lift (M := M) (localizationDerivationSourceDualHom_isUnit (S := S) M D)

/-- The constructed first-order map extends the exact source map. -/
theorem localizationDerivationDualHom_algebraMap (D : Derivation K R R) (r : R) :
    localizationDerivationDualHom (S := S) M D (algebraMap R S r) =
      localizationDerivationSourceDualHom (S := S) D r := IsLocalization.lift_eq _ _

/-- The zeroth-order part is the identity on the localization. -/
theorem localizationDerivationDualHom_fst (D : Derivation K R R) (s : S) :
    (localizationDerivationDualHom (S := S) M D s).fst = s := by
  have he : (TrivSqZeroExt.fstHom S S S).toRingHom.comp
      (localizationDerivationDualHom (S := S) M D) = RingHom.id S := by
    apply IsLocalization.ringHom_ext M
    ext r
    simp [localizationDerivationDualHom_algebraMap, localizationDerivationSourceDualHom]
  exact congrArg (fun f : S →+* S => f s) he

/-- The first-order component of the constructed localized map. -/
noncomputable def localizationDerivationValue (D : Derivation K R R) (s : S) : S :=
  (localizationDerivationDualHom (S := S) M D s).snd

/-- The localization derivative retains every original regular value. -/
theorem localizationDerivationValue_algebraMap (D : Derivation K R R) (r : R) :
    localizationDerivationValue (S := S) M D (algebraMap R S r) = algebraMap R S (D r) := by
  simp [localizationDerivationValue, localizationDerivationDualHom_algebraMap,
    localizationDerivationSourceDualHom, Algebra.smul_def]

/-- Additivity holds on all localized values, not only on generators. -/
theorem localizationDerivationValue_add (D : Derivation K R R) (s t : S) :
    localizationDerivationValue (S := S) M D (s + t) =
      localizationDerivationValue (S := S) M D s + localizationDerivationValue (S := S) M D t := by
  simp [localizationDerivationValue]

/-- The localized first-order homomorphism gives the full product rule. -/
theorem localizationDerivationValue_mul (D : Derivation K R R) (s t : S) :
    localizationDerivationValue (S := S) M D (s * t) =
      s * localizationDerivationValue (S := S) M D t + t * localizationDerivationValue (S := S) M D s := by
  simp only [localizationDerivationValue, map_mul, TrivSqZeroExt.snd_mul,
    localizationDerivationDualHom_fst, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

/-- The original base coefficients remain derivative constants. -/
theorem localizationDerivationValue_constant (D : Derivation K R R) (c : K) :
    localizationDerivationValue (S := S) M D (algebraMap K S c) = 0 := by
  rw [IsScalarTower.algebraMap_apply K R S, localizationDerivationValue_algebraMap,
    D.map_algebraMap, map_zero]

/-- The actual localized base-linear derivation, without an assumed
stability or a supplied regular-fraction derivative operator. -/
noncomputable def localizationDerivation (D : Derivation K R R) : Derivation K S S where
  toFun := localizationDerivationValue (S := S) M D
  map_add' := localizationDerivationValue_add M D
  map_smul' c s := by
    simp only [RingHom.id_apply, Algebra.smul_def, localizationDerivationValue_mul, localizationDerivationValue_constant,
      mul_zero, add_zero]
  map_one_eq_zero' := by
    change localizationDerivationValue (S := S) M D (1 : S) = 0
    simpa only [map_one] using localizationDerivationValue_constant (S := S) M D (1 : K)
  leibniz' s t := by
    change localizationDerivationValue (S := S) M D (s * t) =
      s • localizationDerivationValue (S := S) M D t + t • localizationDerivationValue (S := S) M D s
    simpa only [smul_eq_mul] using localizationDerivationValue_mul (S := S) M D s t

/-- The bundled derivative preserves the original source realization. -/
theorem localizationDerivation_algebraMap (D : Derivation K R R) (r : R) :
    localizationDerivation (S := S) M D (algebraMap R S r) = algebraMap R S (D r) :=
  localizationDerivationValue_algebraMap M D r

end DimensionFourDependence
