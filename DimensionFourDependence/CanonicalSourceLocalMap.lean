import DimensionFourDependence.LocalEquivRationalOrder

/-! # Source orders for the canonical map on local rings

The map recovered through the normal etale model is the canonical
localization map induced by the original source ring inclusion.
Thus the regular and rational order comparisons concern the actual
map on local rings, independently of the chosen normal model.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {R T B : Type*} [CommRing R] [CommRing T] [CommRing B]
  [Algebra R T] [Algebra R B]
  (Q : Ideal R) [Q.IsPrime] (q : Ideal T) [q.IsPrime] [q.LiesOver Q]
  [Algebra (Localization.AtPrime Q) B] [IsScalarTower R (Localization.AtPrime Q) B]

/-- A source-compatible local model gives exactly the canonical
source localization map on the original normalization local ring. -/
theorem localEquivSourceAlgHom_eq_canonical_localRingHom
    (e : Localization.AtPrime q ≃ₐ[R] B) :
    (localEquivSourceAlgHom (O := Localization.AtPrime Q) e).toRingHom =
      Localization.localRingHom Q q (algebraMap R T) (Ideal.over_def q Q) := by
  symm
  apply Localization.localRingHom_unique
  intro r
  change localEquivSourceAlgHom (O := Localization.AtPrime Q) e
    (algebraMap R (Localization.AtPrime Q) r) = _
  rw [localEquivSourceAlgHom_original_source]
  exact IsScalarTower.algebraMap_apply R T (Localization.AtPrime q) r

variable [IsDomain R] [IsDiscreteValuationRing (Localization.AtPrime Q)]
  [IsDomain T] [IsDomain B] [IsDiscreteValuationRing B]
  [Module.IsTorsionFree (Localization.AtPrime Q) B]
  [Algebra.EssFiniteType (Localization.AtPrime Q) B]
  [Algebra.FormallyUnramified (Localization.AtPrime Q) B]
  [IsLocalHom (algebraMap (Localization.AtPrime Q) B)]

/-- Exact regular vanishing bounds for the canonical local-ring map. -/
theorem canonical_localRingHom_maximalIdeal_pow_mem_iff
    (e : Localization.AtPrime q ≃ₐ[R] B) (x : Localization.AtPrime Q) (a : ℕ) :
    Localization.localRingHom Q q (algebraMap R T) (Ideal.over_def q Q) x ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ a ↔
        x ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ a := by
  rw [← localEquivSourceAlgHom_eq_canonical_localRingHom Q q e]
  exact localEquivSource_maximalIdeal_pow_mem_iff (O := Localization.AtPrime Q) e x a

variable {F : Type*} [Field F] [Algebra (Localization.AtPrime Q) F]
  [IsFractionRing (Localization.AtPrime Q) F]

/-- The rational pullback extends the canonical local-ring map and
preserves every normalized rational source divisor order. -/
theorem canonical_localRingHom_rational_order
    (e : Localization.AtPrime q ≃ₐ[R] B) :
    letI : Algebra (Localization.AtPrime q) (FractionRing (Localization.AtPrime q)) :=
      OreLocalization.instAlgebra
    ∃ j : F →+* FractionRing (Localization.AtPrime q),
      (∀ x : Localization.AtPrime Q,
        j (algebraMap (Localization.AtPrime Q) F x) =
          algebraMap (Localization.AtPrime q) (FractionRing (Localization.AtPrime q))
            (Localization.localRingHom Q q (algebraMap R T) (Ideal.over_def q Q) x)) ∧
      letI : IsDiscreteValuationRing (Localization.AtPrime q) :=
        local_equiv_isDiscreteValuationRing e.toRingEquiv
      let v : IsDedekindDomain.HeightOneSpectrum (Localization.AtPrime Q) :=
        ⟨IsLocalRing.maximalIdeal _, inferInstance, IsDiscreteValuationRing.not_a_field _⟩
      let w : IsDedekindDomain.HeightOneSpectrum (Localization.AtPrime q) :=
        ⟨IsLocalRing.maximalIdeal _, inferInstance, IsDiscreteValuationRing.not_a_field _⟩
      ∀ x : F, v.valuation F x = w.valuation (FractionRing (Localization.AtPrime q)) (j x) := by
  let : Algebra (Localization.AtPrime q) (FractionRing (Localization.AtPrime q)) :=
    OreLocalization.instAlgebra
  let : Algebra (Localization.AtPrime Q) (Localization.AtPrime q) :=
    localEquivSourceAlgebra (O := Localization.AtPrime Q) e
  refine ⟨(localEquivSourceFractionHom (O := Localization.AtPrime Q) (F := F) e).toRingHom,
    ?_, localEquivSource_rational_order (O := Localization.AtPrime Q) (F := F) e⟩
  intro x
  change localEquivSourceFractionHom (O := Localization.AtPrime Q) (F := F) e
    (algebraMap (Localization.AtPrime Q) F x) = _
  rw [localEquivSourceFractionHom_algebraMap,
    ← localEquivSourceAlgHom_eq_canonical_localRingHom Q q e]
  rfl

end DimensionFourDependence
