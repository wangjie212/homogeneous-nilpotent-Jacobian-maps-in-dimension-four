import DimensionFourDependence.LocalEquivUnramifiedSource

/-! # Normalized rational orders on the actual normalization local ring

The constructed original-source local action makes the normalization
local ring itself an unramified DVR extension. Its normalized valuation
therefore agrees on every rational source function, and maximal-ideal
power bounds agree on every regular source-local function.
-/

namespace DimensionFourDependence

variable {R O A B : Type*} [CommRing R]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing A] [IsDomain A] [IsLocalRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra R O] [Algebra R A] [Algebra R B] [Algebra O B] [IsScalarTower R O B]
  [Module.IsTorsionFree O B] [Algebra.EssFiniteType O B]
  [Algebra.FormallyUnramified O B] [IsLocalHom (algebraMap O B)]

/-- Exact vanishing-order bounds for the constructed source-local
map into the original normalization local ring. -/
theorem localEquivSource_maximalIdeal_pow_mem_iff (e : A ≃ₐ[R] B) (x : O) (a : ℕ) :
    localEquivSourceAlgHom (O := O) e x ∈ (IsLocalRing.maximalIdeal A) ^ a ↔
      x ∈ (IsLocalRing.maximalIdeal O) ^ a := by
  let : Algebra O A := localEquivSourceAlgebra (O := O) e
  obtain ⟨hdvr, htf, hft, hunr, hlocal⟩ := localEquivSource_unramified_structure (O := O) e
  let : IsDiscreteValuationRing A := hdvr
  let : Module.IsTorsionFree O A := htf
  let : Algebra.EssFiniteType O A := hft
  let : Algebra.FormallyUnramified O A := hunr
  let : IsLocalHom (algebraMap O A) := hlocal
  let : (IsLocalRing.maximalIdeal A).LiesOver (IsLocalRing.maximalIdeal O) :=
    (Ideal.liesOver_iff _ _).mpr (IsLocalRing.maximalIdeal_comap (algebraMap O A)).symm
  let v : IsDedekindDomain.HeightOneSpectrum O :=
    ⟨IsLocalRing.maximalIdeal O, inferInstance, IsDiscreteValuationRing.not_a_field O⟩
  let w : IsDedekindDomain.HeightOneSpectrum A :=
    ⟨IsLocalRing.maximalIdeal A, inferInstance, IsDiscreteValuationRing.not_a_field A⟩
  change algebraMap O A x ∈ w.asIdeal ^ a ↔ x ∈ v.asIdeal ^ a
  rw [← w.intValuation_le_pow_iff_mem, ← v.intValuation_le_pow_iff_mem,
    unramified_divisor_intValuation v w]

variable {F : Type*} [Field F] [Algebra O F] [IsFractionRing O F]

/-- Complete rational source-order equality with its constructed actual
source-field pullback into the normalization local fraction field. -/
noncomputable def LocalEquivSourceRationalOrder (e : A ≃ₐ[R] B) : Prop :=
  letI : Algebra O A := localEquivSourceAlgebra (O := O) e
  letI : IsDiscreteValuationRing A := local_equiv_isDiscreteValuationRing e.toRingEquiv
  let v : IsDedekindDomain.HeightOneSpectrum O :=
    ⟨IsLocalRing.maximalIdeal O, inferInstance, IsDiscreteValuationRing.not_a_field O⟩
  let w : IsDedekindDomain.HeightOneSpectrum A :=
    ⟨IsLocalRing.maximalIdeal A, inferInstance, IsDiscreteValuationRing.not_a_field A⟩
  ∀ x : F, v.valuation F x = w.valuation (FractionRing A)
    (localEquivSourceFractionHom (O := O) (F := F) e x)

/-- The normalized divisor order of every original rational source
function agrees at the normalization prime and the source divisor. -/
theorem localEquivSource_rational_order (e : A ≃ₐ[R] B) :
    LocalEquivSourceRationalOrder (O := O) (F := F) e := by
  let : Algebra O A := localEquivSourceAlgebra (O := O) e
  obtain ⟨hdvr, htf, hft, hunr, hlocal⟩ := localEquivSource_unramified_structure (O := O) e
  let : IsDiscreteValuationRing A := hdvr
  let : Module.IsTorsionFree O A := htf
  let : Algebra.EssFiniteType O A := hft
  let : Algebra.FormallyUnramified O A := hunr
  let : IsLocalHom (algebraMap O A) := hlocal
  let : (IsLocalRing.maximalIdeal A).LiesOver (IsLocalRing.maximalIdeal O) :=
    (Ideal.liesOver_iff _ _).mpr (IsLocalRing.maximalIdeal_comap (algebraMap O A)).symm
  let j : F →ₐ[O] FractionRing A := localEquivSourceFractionHom (O := O) (F := F) e
  let : Algebra F (FractionRing A) := j.toRingHom.toAlgebra
  let : IsScalarTower O F (FractionRing A) := IsScalarTower.of_algebraMap_eq
    (fun x => (j.commutes x).symm)
  let v : IsDedekindDomain.HeightOneSpectrum O :=
    ⟨IsLocalRing.maximalIdeal O, inferInstance, IsDiscreteValuationRing.not_a_field O⟩
  let w : IsDedekindDomain.HeightOneSpectrum A :=
    ⟨IsLocalRing.maximalIdeal A, inferInstance, IsDiscreteValuationRing.not_a_field A⟩
  intro x
  exact unramified_divisor_rational_valuation v w x

end DimensionFourDependence
