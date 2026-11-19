import DimensionFourDependence.Defs
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-! # Finite normalization of finitely generated characteristic-zero domains

Noether normalization supplies an integral polynomial subring. The source
fraction field is finite separable over that subring's fraction field.
The trace-dual-basis finiteness theorem then bounds the integral closure
over the polynomial subring and hence over the original domain.
-/

namespace DimensionFourDependence

variable {K A F : Type*} [Field K] [CharZero K] [CommRing A] [IsDomain A]
  [Field F] [Algebra K A] [Algebra A F]
  [IsFractionRing A F] [Algebra.FiniteType K A]

attribute [local instance] FractionRing.liftAlgebra

include K in
/-- The integral closure of a finitely generated characteristic-zero
domain in its actual fraction field is finite over that domain. -/
theorem finite_normalization_of_finiteType : Module.Finite A (integralClosure A F) := by
  obtain ⟨n, g, hg, hgfin⟩ := exists_finite_inj_algHom_of_fg K A
  let B := MvPolynomial (Fin n) K
  let L := FractionRing B
  let C := integralClosure A F
  let : Algebra B A := g.toRingHom.toAlgebra
  let : Algebra B F := ((algebraMap A F).comp g.toRingHom).toAlgebra
  let : IsScalarTower B A F := IsScalarTower.of_algebraMap_eq (by intro b; rfl)
  let : Module.Finite B A := hgfin
  let : Algebra.IsIntegral B A := inferInstance
  have hinj : Function.Injective (algebraMap B F) :=
    (IsFractionRing.injective A F).comp hg
  let : FaithfulSMul B F := (faithfulSMul_iff_algebraMap_injective B F).mpr hinj
  let : Algebra L F := FractionRing.liftAlgebra B F
  let : IsScalarTower B L F := FractionRing.isScalarTower_liftAlgebra B F
  let : Algebra.IsAlgebraic L F := isAlgebraic_of_isFractionRing B A L F
  let : Algebra.EssFiniteType A F :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors A)
  let : Algebra.EssFiniteType B F := Algebra.EssFiniteType.comp B A F
  let : Algebra.EssFiniteType L F := Algebra.EssFiniteType.of_comp B L F
  let : Module.Finite L F := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let : Algebra B C := ((algebraMap A C).comp g.toRingHom).toAlgebra
  let : IsScalarTower B A C := IsScalarTower.of_algebraMap_eq (by intro b; rfl)
  let : IsScalarTower B C F := IsScalarTower.of_algebraMap_eq (by intro b; rfl)
  let : IsIntegralClosure C B F := by
    refine ⟨Subtype.val_injective, ?_⟩
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx.tower_top⟩, rfl⟩
    · rintro ⟨c, rfl⟩
      exact isIntegral_trans (R := B) (A := A) _ c.property
  let : Module.Finite B C := IsIntegralClosure.finite B L F C
  exact Module.Finite.of_restrictScalars_finite B A C

end DimensionFourDependence
