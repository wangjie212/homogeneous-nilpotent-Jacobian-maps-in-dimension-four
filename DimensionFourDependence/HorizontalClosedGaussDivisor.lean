import DimensionFourDependence.ResidueTranscendentalParameter
import DimensionFourDependence.UnramifiedDvrBaseChange
import DimensionFourDependence.RationalClosedGaussCover
import DimensionFourDependence.SourceDivisorLocalization
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Horizontal divisors for the actual relatively closed Gauss cover

The parameter field used here is the actual intermediate field in the
original rational source. A transcendental residue of its rational
parameter embeds that same field in the source divisor DVR. This supplies
the scalar tower needed to apply the finite étale base change theorem.
The condition that a geometric curve gives this horizontal divisor still
requires a separate construction of its contraction in the source.
-/

namespace DimensionFourDependence

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

local notation "R" => MvPolynomial (Fin 4) K
local notation "F" => FractionRing (MvPolynomial (Fin 4) K)

variable {A : Type*} [CommRing A] [Algebra K A] [IsLocalRing A]

/-- The actual closed Gauss field embeds into a local source ring when
its rational parameter has transcendental residue there. -/
noncomputable def closedGaussHorizontalLocalHom
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (t : A) (ht : Transcendental K (IsLocalRing.residue A t)) :
    closedGaussParameterField H I →ₐ[K] A :=
  (horizontalParameterHom t ht).comp e.symm.toAlgHom

variable [Algebra A (FractionRing (MvPolynomial (Fin 4) K))]
  [IsScalarTower K A (FractionRing (MvPolynomial (Fin 4) K))]

/-- Realizing the local embedding in the source field gives exactly the
original inclusion of the relatively closed Gauss parameter field. -/
theorem closedGaussHorizontalLocalHom_source
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (t : A) (ht : Transcendental K (IsLocalRing.residue A t))
    (hX : algebraMap A F t = closedGaussParameterSourceHom H I e RatFunc.X) :
    (IsScalarTower.toAlgHom K A F).comp (closedGaussHorizontalLocalHom H I e t ht) =
      (closedGaussParameterField H I).val := by
  have hc := horizontalParameterHom_comp_source t ht (closedGaussParameterSourceHom H I e) hX
  ext c
  have h := AlgHom.congr_fun hc (e.symm c)
  change algebraMap A F (horizontalParameterHom t ht (e.symm c)) = _ at h ⊢
  simpa only [closedGaussParameterSourceHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    e.apply_symm_apply] using h

/-- The local closed-parameter algebra structure is compatible with the
actual closed-field action on the original source function field. -/
theorem closedGaussHorizontalLocalHom_scalarTower
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (t : A) (ht : Transcendental K (IsLocalRing.residue A t))
    (hX : algebraMap A F t = closedGaussParameterSourceHom H I e RatFunc.X) :
    letI : Algebra (closedGaussParameterField H I) A :=
      (closedGaussHorizontalLocalHom H I e t ht).toRingHom.toAlgebra
    IsScalarTower (closedGaussParameterField H I) A F := by
  let : Algebra (closedGaussParameterField H I) A :=
    (closedGaussHorizontalLocalHom H I e t ht).toRingHom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (AlgHom.congr_fun (closedGaussHorizontalLocalHom_source H I e t ht hX) c).symm

variable [CharZero K]

/-- Finite coefficient extensions of the actual horizontal source divisor
are Dedekind domains. Normality is proved from the constructed parameter
embedding and relative closedness in the original source function field. -/
theorem actual_closed_gauss_horizontal_divisor_base_change_dedekind
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (Q : Ideal R) [Q.IsPrime] (f : R) (hf : Irreducible f) (hQ : Q = Ideal.span {f})
    (t : Localization.AtPrime Q)
    (ht : Transcendental K (IsLocalRing.residue (Localization.AtPrime Q) t))
    (hX : algebraMap (Localization.AtPrime Q) F t = closedGaussParameterSourceHom H I e RatFunc.X)
    (E : Type*) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Module.Finite (closedGaussParameterField H I) E] :
    letI : Algebra (closedGaussParameterField H I) (Localization.AtPrime Q) :=
      (closedGaussHorizontalLocalHom H I e t ht).toRingHom.toAlgebra
    IsDedekindDomain (Localization.AtPrime Q ⊗[closedGaussParameterField H I] E) := by
  let : CharZero (closedGaussParameterField H I) :=
    charZero_of_injective_algebraMap (algebraMap K (closedGaussParameterField H I)).injective
  let : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    principal_prime_localization_isDVR Q f (irreducible_iff_prime.mp hf) hQ
  let : Algebra (closedGaussParameterField H I) (Localization.AtPrime Q) :=
    (closedGaussHorizontalLocalHom H I e t ht).toRingHom.toAlgebra
  let : IsScalarTower K (Localization.AtPrime Q) F :=
    IsScalarTower.of_algebraMap_eq (by
      intro c
      rw [IsScalarTower.algebraMap_apply K R F,
        IsScalarTower.algebraMap_apply K R (Localization.AtPrime Q),
        IsScalarTower.algebraMap_apply R (Localization.AtPrime Q) F])
  let : IsScalarTower (closedGaussParameterField H I) (Localization.AtPrime Q) F :=
    closedGaussHorizontalLocalHom_scalarTower H I e t ht hX
  exact relatively_closed_dvr_base_change_dedekind (closedGaussParameterField_relatively_closed H I)

/-- The order-to-common-factor conclusion for a finite coefficient
extension of an actual horizontal source divisor. All normality and
unramifiedness assumptions are discharged by the constructed local model. -/
theorem actual_closed_gauss_horizontal_orders_common_factor_degree
    (H V : Fin 4 → R) (I : ImageRelationWitness H)
    (g : R) (hg : g ≠ 0) (hV : IsPrimitiveVec V) (hHV : H = fun i => g * V i)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (Q : Ideal R) [Q.IsPrime] (f : R) (hf : Irreducible f) (hQ : Q = Ideal.span {f})
    (t : Localization.AtPrime Q)
    (ht : Transcendental K (IsLocalRing.residue (Localization.AtPrime Q) t))
    (hX : algebraMap (Localization.AtPrime Q) F t = closedGaussParameterSourceHom H I e RatFunc.X)
    (E : Type*) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Module.Finite (closedGaussParameterField H I) E] :
    letI : Algebra (closedGaussParameterField H I) (Localization.AtPrime Q) :=
      (closedGaussHorizontalLocalHom H I e t ht).toRingHom.toAlgebra
    letI : IsDedekindDomain (Localization.AtPrime Q ⊗[closedGaussParameterField H I] E) :=
      actual_closed_gauss_horizontal_divisor_base_change_dedekind H I e Q f hf hQ t ht hX E
    ∀ (w : IsDedekindDomain.HeightOneSpectrum
        (Localization.AtPrime Q ⊗[closedGaussParameterField H I] E))
      [w.asIdeal.LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime Q))] (a : ℕ),
      (∀ i, w.intValuation (algebraMap (Localization.AtPrime Q)
        (Localization.AtPrime Q ⊗[closedGaussParameterField H I] E)
        (algebraMap R (Localization.AtPrime Q) (H i))) ≤ WithZero.exp (-(a : ℤ))) →
      f ^ a ∣ g ∧ a * f.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  let : Algebra (closedGaussParameterField H I) (Localization.AtPrime Q) :=
    (closedGaussHorizontalLocalHom H I e t ht).toRingHom.toAlgebra
  let : IsDedekindDomain (Localization.AtPrime Q ⊗[closedGaussParameterField H I] E) :=
    actual_closed_gauss_horizontal_divisor_base_change_dedekind H I e Q f hf hQ t ht hX E
  let : CharZero (closedGaussParameterField H I) :=
    charZero_of_injective_algebraMap (algebraMap K (closedGaussParameterField H I)).injective
  obtain ⟨hfinite, hetale⟩ := finite_coefficient_base_change_etale
    (k := closedGaussParameterField H I) (A := Localization.AtPrime Q) (E := E)
  let : Module.Finite (Localization.AtPrime Q)
      (Localization.AtPrime Q ⊗[closedGaussParameterField H I] E) := hfinite
  let : Algebra.Etale (Localization.AtPrime Q)
      (Localization.AtPrime Q ⊗[closedGaussParameterField H I] E) := hetale
  intro w hlie a horder
  exact unramified_source_orders_common_factor_degree H V g hg hV hHV Q f hf hQ _ w a horder

end DimensionFourDependence
