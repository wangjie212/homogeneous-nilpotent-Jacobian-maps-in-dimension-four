import DimensionFourDependence.HorizontalClosedGaussDivisor
import DimensionFourDependence.PencilDivisorParameter

/-! # The horizontal divisor local model from the actual pencil quotient

The original quotient p/q supplies the local parameter and its source
realization. The remaining hypothesis is precisely that its residue in
the source divisor field is transcendental. Under that horizontal
condition, finite coefficient extensions are normal and the upstairs
component orders force the original common-factor degree bound.
-/

namespace DimensionFourDependence

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

local notation "R" => MvPolynomial (Fin 4) K
local notation "F" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual closed Gauss parameter field in the source divisor local
ring, defined from the original pencil numerator and denominator. -/
noncomputable def closedGaussPencilDivisorHom
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (Q : Ideal R) [Q.IsPrime] (p q : R) (hq : q ∉ Q)
    (hhor : Transcendental K
      (IsLocalRing.residue (Localization.AtPrime Q) (algebraMap R (Localization.AtPrime Q) p) /
        IsLocalRing.residue (Localization.AtPrime Q) (algebraMap R (Localization.AtPrime Q) q))) :
    closedGaussParameterField H I →ₐ[K] Localization.AtPrime Q :=
  closedGaussHorizontalLocalHom H I e (pencilDivisorParameter Q p q hq)
    (by rwa [pencilDivisorParameter_residue])

variable [CharZero K]

/-- The actual finite coefficient base change at a horizontal source
divisor is normal, using the parameter p/q from the original source. -/
theorem actual_pencil_horizontal_divisor_base_change_dedekind
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (Q : Ideal R) [Q.IsPrime] (f : R) (hf : Irreducible f) (hQ : Q = Ideal.span {f})
    (p q : R) (hq : q ∉ Q)
    (hrep : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap R F p / algebraMap R F q)
    (hhor : Transcendental K
      (IsLocalRing.residue (Localization.AtPrime Q) (algebraMap R (Localization.AtPrime Q) p) /
        IsLocalRing.residue (Localization.AtPrime Q) (algebraMap R (Localization.AtPrime Q) q)))
    (E : Type*) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Module.Finite (closedGaussParameterField H I) E] :
    letI : Algebra (closedGaussParameterField H I) (Localization.AtPrime Q) :=
      (closedGaussPencilDivisorHom H I e Q p q hq hhor).toRingHom.toAlgebra
    IsDedekindDomain (Localization.AtPrime Q ⊗[closedGaussParameterField H I] E) := by
  exact actual_closed_gauss_horizontal_divisor_base_change_dedekind H I e Q f hf hQ
    (pencilDivisorParameter Q p q hq) (by rwa [pencilDivisorParameter_residue])
    ((pencilDivisorParameter_source Q p q hq).trans hrep.symm) E

/-- Orders on a finite coefficient extension of the actual pencil's
horizontal source divisor force the common-factor degree bound. The
local parameter, normality and unramifiedness are constructed here. -/
theorem actual_pencil_horizontal_orders_common_factor_degree
    (H V : Fin 4 → R) (I : ImageRelationWitness H)
    (g : R) (hg : g ≠ 0) (hV : IsPrimitiveVec V) (hHV : H = fun i => g * V i)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (Q : Ideal R) [Q.IsPrime] (f : R) (hf : Irreducible f) (hQ : Q = Ideal.span {f})
    (p q : R) (hq : q ∉ Q)
    (hrep : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap R F p / algebraMap R F q)
    (hhor : Transcendental K
      (IsLocalRing.residue (Localization.AtPrime Q) (algebraMap R (Localization.AtPrime Q) p) /
        IsLocalRing.residue (Localization.AtPrime Q) (algebraMap R (Localization.AtPrime Q) q)))
    (E : Type*) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Module.Finite (closedGaussParameterField H I) E] :
    letI : Algebra (closedGaussParameterField H I) (Localization.AtPrime Q) :=
      (closedGaussPencilDivisorHom H I e Q p q hq hhor).toRingHom.toAlgebra
    letI : IsDedekindDomain (Localization.AtPrime Q ⊗[closedGaussParameterField H I] E) :=
      actual_pencil_horizontal_divisor_base_change_dedekind H I e Q f hf hQ p q hq hrep hhor E
    ∀ (w : IsDedekindDomain.HeightOneSpectrum
        (Localization.AtPrime Q ⊗[closedGaussParameterField H I] E))
      [w.asIdeal.LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime Q))] (a : ℕ),
      (∀ i, w.intValuation (algebraMap (Localization.AtPrime Q)
        (Localization.AtPrime Q ⊗[closedGaussParameterField H I] E)
        (algebraMap R (Localization.AtPrime Q) (H i))) ≤ WithZero.exp (-(a : ℤ))) →
      f ^ a ∣ g ∧ a * f.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  exact actual_closed_gauss_horizontal_orders_common_factor_degree H V I g hg hV hHV e Q f hf hQ
    (pencilDivisorParameter Q p q hq) (by rwa [pencilDivisorParameter_residue])
    ((pencilDivisorParameter_source Q p q hq).trans hrep.symm) E

end DimensionFourDependence
