import DimensionFourDependence.ResidueTranscendentalParameter
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # The actual pencil quotient in a source divisor localization

Away from the pencil denominator, its quotient is a regular element of
the source divisor local ring. Its images in the source function field
and in the divisor residue field are the expected quotients. Thus the
horizontal residue condition supplies the full local parameter-field
embedding, without a separately chosen local parameter.
-/

namespace DimensionFourDependence

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]
  (Q : Ideal R) [Q.IsPrime]

/-- The pencil quotient as an element of the actual source divisor local
ring, on the chart where the denominator does not vanish. -/
noncomputable def pencilDivisorParameter (p q : R) (hq : q ∉ Q) : Localization.AtPrime Q :=
  IsLocalization.mk' (M := Q.primeCompl) (Localization.AtPrime Q) p ⟨q, hq⟩

/-- The constructed local parameter realizes the original source
rational function, with the canonical localization-to-source map. -/
theorem pencilDivisorParameter_source [IsDomain R] (p q : R) (hq : q ∉ Q) :
    algebraMap (Localization.AtPrime Q) (FractionRing R) (pencilDivisorParameter Q p q hq) =
      algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) q := by
  have hq0 : q ≠ 0 := fun hz => hq (hz ▸ Q.zero_mem)
  have hs := congrArg (algebraMap (Localization.AtPrime Q) (FractionRing R))
    (IsLocalization.mk'_spec (M := Q.primeCompl) (Localization.AtPrime Q) p ⟨q, hq⟩)
  simp only [map_mul, ← IsScalarTower.algebraMap_apply R (Localization.AtPrime Q) (FractionRing R)] at hs
  have hqF : algebraMap R (FractionRing R) q ≠ 0 := by
    intro hz
    apply hq0
    exact IsFractionRing.injective R (FractionRing R) (by simpa using hz)
  exact (eq_div_iff hqF).mpr hs

/-- The actual pencil denominator stays nonzero in the divisor residue
field precisely because it is outside the source divisor prime. -/
theorem pencilDivisorParameter_denominator_residue_ne_zero (q : R) (hq : q ∉ Q) :
    IsLocalRing.residue (Localization.AtPrime Q) (algebraMap R (Localization.AtPrime Q) q) ≠ 0 := by
  rw [ne_eq, IsLocalRing.residue_eq_zero_iff,
    IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q q]
  exact hq

/-- Specializing the regular pencil quotient to the divisor gives the
quotient of its specialized original-source numerator and denominator. -/
theorem pencilDivisorParameter_residue (p q : R) (hq : q ∉ Q) :
    IsLocalRing.residue (Localization.AtPrime Q) (pencilDivisorParameter Q p q hq) =
      IsLocalRing.residue (Localization.AtPrime Q) (algebraMap R (Localization.AtPrime Q) p) /
        IsLocalRing.residue (Localization.AtPrime Q) (algebraMap R (Localization.AtPrime Q) q) := by
  have hs := congrArg (IsLocalRing.residue (Localization.AtPrime Q))
    (IsLocalization.mk'_spec (M := Q.primeCompl) (Localization.AtPrime Q) p ⟨q, hq⟩)
  rw [map_mul] at hs
  exact (eq_div_iff (pencilDivisorParameter_denominator_residue_ne_zero Q q hq)).mpr hs

/-- A horizontal source divisor embeds the whole rational parameter
field through its original pencil quotient in the divisor local ring. -/
noncomputable def horizontalPencilDivisorParameterHom (p q : R) (hq : q ∉ Q)
    (hhor : Transcendental K
      (IsLocalRing.residue (Localization.AtPrime Q) (algebraMap R (Localization.AtPrime Q) p) /
        IsLocalRing.residue (Localization.AtPrime Q) (algebraMap R (Localization.AtPrime Q) q))) :
    RatFunc K →ₐ[K] Localization.AtPrime Q :=
  horizontalParameterHom (pencilDivisorParameter Q p q hq)
    (by rwa [pencilDivisorParameter_residue])

end DimensionFourDependence
