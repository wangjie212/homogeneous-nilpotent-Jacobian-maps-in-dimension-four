import DimensionFourDependence.DedekindLocalOverring
import DimensionFourDependence.ResidueParameterField

/-! # The actual source parameter DVR at a nonzero vanishing coordinate

A regular coefficient field and a local coordinate in the maximal ideal
construct the source parameter DVR and its actual local map. The source
uniformizer maps to the specified original coordinate.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable (k : Type*) [Field k]

/-- The origin prime of the actual one-variable parameter ring. -/
noncomputable def polynomialParameterZeroPrime : PrimeSpectrum (Polynomial k) :=
  ⟨Ideal.span {Polynomial.X}, Ideal.isPrime_span_singleton_of_prime Polynomial.prime_X⟩

local notation "p₀" => PrimeSpectrum.asIdeal (polynomialParameterZeroPrime k)

/-- The source parameter prime is nonzero. -/
theorem polynomialParameterZeroPrime_ne_bot : p₀ ≠ ⊥ := by
  intro h
  have hx : (Polynomial.X : Polynomial k) ∈ p₀ := Ideal.subset_span (by simp)
  rw [h] at hx
  exact Polynomial.X_ne_zero (Ideal.mem_bot.mp hx)

/-- The actual parameter localization is a DVR. -/
theorem polynomialParameterLocalRing_isDVR : IsDiscreteValuationRing (Localization.AtPrime p₀) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial k)
    (polynomialParameterZeroPrime_ne_bot k) _

/-- The actual source parameter is a uniformizer of that DVR. -/
theorem polynomialParameterLocal_X_irreducible :
    Irreducible (algebraMap (Polynomial k) (Localization.AtPrime p₀) Polynomial.X) := by
  let : IsDiscreteValuationRing (Localization.AtPrime p₀) := polynomialParameterLocalRing_isDVR k
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
  calc
    IsLocalRing.maximalIdeal (Localization.AtPrime p₀) = (p₀).map (algebraMap _ _) :=
      (Localization.AtPrime.map_eq_maximalIdeal (I := p₀)).symm
    _ = _ := by
      change (Ideal.span {Polynomial.X}).map _ = _
      rw [Ideal.map_span, Set.image_singleton]

variable {k} {B : Type*} [CommRing B] [IsLocalRing B] [Algebra k B]

/-- Evaluating at a vanishing local coordinate contracts the actual
target maximal ideal to precisely the source parameter origin prime. -/
theorem local_parameter_evaluation_maximalIdeal
    (z : B) (hz : z ∈ IsLocalRing.maximalIdeal B) :
    (IsLocalRing.maximalIdeal B).comap (Polynomial.aeval z).toRingHom =
      (polynomialParameterZeroPrime k).asIdeal := by
  ext p
  change Polynomial.aeval z p ∈ IsLocalRing.maximalIdeal B ↔ _
  rw [← IsLocalRing.residue_eq_zero_iff]
  let f : B →ₐ[k] IsLocalRing.ResidueField B := IsScalarTower.toAlgHom k B _
  have he : IsLocalRing.residue B (Polynomial.aeval z p) =
      algebraMap k (IsLocalRing.ResidueField B) p.constantCoeff := by
    change f (Polynomial.aeval z p) = _
    rw [← Polynomial.aeval_algHom_apply f z p]
    change Polynomial.aeval (IsLocalRing.residue B z) p = _
    rw [(IsLocalRing.residue_eq_zero_iff z).mpr hz]
    simp only [Polynomial.aeval_def, Polynomial.eval₂_at_zero, Polynomial.constantCoeff_apply]
  rw [he]
  change algebraMap k (IsLocalRing.ResidueField B) p.constantCoeff = 0 ↔
    p ∈ Ideal.span {Polynomial.X}
  rw [← Polynomial.ker_constantCoeff]
  change algebraMap k (IsLocalRing.ResidueField B) p.constantCoeff = 0 ↔ p.constantCoeff = 0
  exact map_eq_zero (algebraMap k (IsLocalRing.ResidueField B))

/-- The coordinate supplies an actual local map from its source
parameter DVR to the given geometric local ring. -/
noncomputable def localParameterDvrHom
    (z : B) (hz : z ∈ IsLocalRing.maximalIdeal B) :
    Localization.AtPrime (polynomialParameterZeroPrime k).asIdeal →+* B := by
  let : Algebra (Polynomial k) B := (Polynomial.aeval z).toRingHom.toAlgebra
  exact (dedekindOverringLocalHom (polynomialParameterZeroPrime k).asIdeal
    (local_parameter_evaluation_maximalIdeal z hz).symm).toRingHom

/-- This constructed map preserves the specified value of every
source parameter polynomial. -/
theorem localParameterDvrHom_polynomial
    (z : B) (hz : z ∈ IsLocalRing.maximalIdeal B) (p : Polynomial k) :
    localParameterDvrHom (k := k) z hz (algebraMap (Polynomial k)
      (Localization.AtPrime (polynomialParameterZeroPrime k).asIdeal) p) = Polynomial.aeval z p := by
  let : Algebra (Polynomial k) B := (Polynomial.aeval z).toRingHom.toAlgebra
  exact (dedekindOverringLocalHom (polynomialParameterZeroPrime k).asIdeal
    (local_parameter_evaluation_maximalIdeal z hz).symm).commutes p

/-- In particular, the actual uniformizer maps to the original
vanishing local coordinate. -/
theorem localParameterDvrHom_X
    (z : B) (hz : z ∈ IsLocalRing.maximalIdeal B) :
    localParameterDvrHom (k := k) z hz (algebraMap (Polynomial k)
      (Localization.AtPrime (polynomialParameterZeroPrime k).asIdeal) Polynomial.X) = z := by
  rw [localParameterDvrHom_polynomial, Polynomial.aeval_X]

/-- The constructed parameter-DVR map dominates the given local ring. -/
theorem localParameterDvrHom_isLocalHom
    (z : B) (hz : z ∈ IsLocalRing.maximalIdeal B) : IsLocalHom (localParameterDvrHom (k := k) z hz) := by
  let : Algebra (Polynomial k) B := (Polynomial.aeval z).toRingHom.toAlgebra
  exact dedekindOverringLocalHom_isLocalHom (polynomialParameterZeroPrime k).asIdeal
    (local_parameter_evaluation_maximalIdeal z hz).symm

end DimensionFourDependence
