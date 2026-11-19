import DimensionFourDependence.RelativelyClosedAlgebraicBaseChange
import DimensionFourDependence.UnramifiedDivisorOrder
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Unramified.Dedekind

/-! # Finite coefficient extensions at horizontal source divisors

Once the parameter field lies inside the source divisor DVR, its finite
coefficient extensions give finite étale base changes. Relative algebraic
closedness of the source function field makes those base changes domains.
They are therefore Dedekind domains already, and their divisor local rings
are unramified DVRs with the same normalized vanishing orders.
-/

namespace DimensionFourDependence

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {k A F E : Type*} [Field k] [CharZero k] [CommRing A]
  [Field F] [Field E] [Algebra k A] [Algebra k F] [Algebra k E]
  [Algebra A F] [IsScalarTower k A F] [FaithfulSMul A F]
  [Module.Finite k E]

/-- Tensoring the inclusion of a source local ring into the relatively
closed source field remains injective, and the resulting ring is a domain. -/
theorem relatively_closed_local_ring_base_change_isDomain
    (hclosed : algebraicClosure k F = ⊥) : IsDomain (A ⊗[k] E) := by
  let j := IsScalarTower.toAlgHom k A F
  let f := Algebra.TensorProduct.map j (AlgHom.id k E)
  have hmap : f.toLinearMap = j.toLinearMap.rTensor E := by
    ext a e
    rfl
  have hi : Function.Injective f := by
    change Function.Injective f.toLinearMap
    rw [hmap]
    exact Module.Flat.rTensor_preserves_injective_linearMap _
      (FaithfulSMul.algebraMap_injective A F)
  let : IsDomain (F ⊗[k] E) :=
    (algebraic_tensor_isField_of_relatively_closed hclosed).isDomain
  exact Function.Injective.isDomain f hi

omit [Algebra k F] [Algebra A F] [IsScalarTower k A F] [FaithfulSMul A F] in
/-- Finite coefficient extensions in characteristic zero give finite
étale algebras over every parameter algebra. -/
theorem finite_coefficient_base_change_etale :
    Module.Finite A (A ⊗[k] E) ∧ Algebra.Etale A (A ⊗[k] E) := by
  let : Algebra.FormallyEtale k E := Algebra.FormallyEtale.of_isSeparable k E
  let : Algebra.FinitePresentation k E :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Etale k E := {}
  exact ⟨inferInstance, inferInstance⟩

variable [IsDomain A] [IsDiscreteValuationRing A]

/-- At a horizontal source DVR the actual coefficient base change is
normal already: it is a finite étale Dedekind domain. -/
theorem relatively_closed_dvr_base_change_dedekind
    (hclosed : algebraicClosure k F = ⊥) : IsDedekindDomain (A ⊗[k] E) := by
  let : IsDomain (A ⊗[k] E) := relatively_closed_local_ring_base_change_isDomain hclosed
  obtain ⟨hfinite, hetale⟩ := finite_coefficient_base_change_etale (k := k) (A := A) (E := E)
  let : Module.Finite A (A ⊗[k] E) := hfinite
  let : Algebra.Etale A (A ⊗[k] E) := hetale
  exact IsDedekindDomain.of_formallyUnramified A _

/-- Localizing the coefficient base change at any prime above the source
divisor gives an unramified DVR, without an additional normality assumption. -/
theorem relatively_closed_dvr_base_change_local
    (hclosed : algebraicClosure k F = ⊥)
    (Q : Ideal (A ⊗[k] E)) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal A)] :
    letI : IsDomain (A ⊗[k] E) := relatively_closed_local_ring_base_change_isDomain hclosed
    IsDiscreteValuationRing (Localization.AtPrime Q) ∧ Algebra.IsUnramifiedAt A Q := by
  let : IsDomain (A ⊗[k] E) := relatively_closed_local_ring_base_change_isDomain hclosed
  let : IsDedekindDomain (A ⊗[k] E) := relatively_closed_dvr_base_change_dedekind hclosed
  obtain ⟨hfinite, hetale⟩ := finite_coefficient_base_change_etale (k := k) (A := A) (E := E)
  let : Module.Finite A (A ⊗[k] E) := hfinite
  let : Algebra.Etale A (A ⊗[k] E) := hetale
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (IsDiscreteValuationRing.not_a_field A) Q
  exact ⟨IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hQ _,
    inferInstance⟩

/-- Every regular source function has the same normalized order at a
divisor of the finite coefficient base change lying above the source DVR. -/
theorem relatively_closed_dvr_base_change_intValuation
    (hclosed : algebraicClosure k F = ⊥) :
    letI : IsDomain (A ⊗[k] E) := relatively_closed_local_ring_base_change_isDomain hclosed
    letI : IsDedekindDomain (A ⊗[k] E) := relatively_closed_dvr_base_change_dedekind hclosed
    ∀ (w : IsDedekindDomain.HeightOneSpectrum (A ⊗[k] E))
      [w.asIdeal.LiesOver (IsLocalRing.maximalIdeal A)] (x : A),
      (⟨IsLocalRing.maximalIdeal A, inferInstance, IsDiscreteValuationRing.not_a_field A⟩ :
        IsDedekindDomain.HeightOneSpectrum A).intValuation x =
        w.intValuation (algebraMap A (A ⊗[k] E) x) := by
  let : IsDomain (A ⊗[k] E) := relatively_closed_local_ring_base_change_isDomain hclosed
  let : IsDedekindDomain (A ⊗[k] E) := relatively_closed_dvr_base_change_dedekind hclosed
  intro w hlie x
  obtain ⟨hfinite, hetale⟩ := finite_coefficient_base_change_etale (k := k) (A := A) (E := E)
  let : Module.Finite A (A ⊗[k] E) := hfinite
  let : Algebra.Etale A (A ⊗[k] E) := hetale
  exact unramified_divisor_intValuation _ w x

/-- A finite coefficient extension actually has an unramified divisor
above the source DVR, and all regular source orders are preserved there. -/
theorem relatively_closed_dvr_base_change_exists_unramified_divisor
    (hclosed : algebraicClosure k F = ⊥) :
    letI : IsDomain (A ⊗[k] E) := relatively_closed_local_ring_base_change_isDomain hclosed
    letI : IsDedekindDomain (A ⊗[k] E) := relatively_closed_dvr_base_change_dedekind hclosed
    ∃ w : IsDedekindDomain.HeightOneSpectrum (A ⊗[k] E),
      w.asIdeal.LiesOver (IsLocalRing.maximalIdeal A) ∧
      IsDiscreteValuationRing (Localization.AtPrime w.asIdeal) ∧
      Algebra.IsUnramifiedAt A w.asIdeal ∧
      ∀ x : A,
        (⟨IsLocalRing.maximalIdeal A, inferInstance, IsDiscreteValuationRing.not_a_field A⟩ :
          IsDedekindDomain.HeightOneSpectrum A).intValuation x =
          w.intValuation (algebraMap A (A ⊗[k] E) x) := by
  let : IsDomain (A ⊗[k] E) := relatively_closed_local_ring_base_change_isDomain hclosed
  let : IsDedekindDomain (A ⊗[k] E) := relatively_closed_dvr_base_change_dedekind hclosed
  obtain ⟨hfinite, hetale⟩ := finite_coefficient_base_change_etale (k := k) (A := A) (E := E)
  let : Module.Finite A (A ⊗[k] E) := hfinite
  let : Algebra.Etale A (A ⊗[k] E) := hetale
  obtain ⟨Q, hQmax, hlie⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := A ⊗[k] E) (IsLocalRing.maximalIdeal A)
  let : Q.IsPrime := hQmax.isPrime
  let : Q.LiesOver (IsLocalRing.maximalIdeal A) := hlie
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (IsDiscreteValuationRing.not_a_field A) Q
  let w : IsDedekindDomain.HeightOneSpectrum (A ⊗[k] E) := ⟨Q, inferInstance, hQ⟩
  refine ⟨w, hlie, (relatively_closed_dvr_base_change_local hclosed Q).1,
    inferInstance, ?_⟩
  exact relatively_closed_dvr_base_change_intValuation hclosed w

end DimensionFourDependence
