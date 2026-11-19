import DimensionFourDependence.PolynomialProjectiveBase
import DimensionFourDependence.OriginalProjectiveChartRing
import DimensionFourDependence.AffineCoordinateStalk

/-! # Integral and Noetherian original projective source -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry TopologicalSpace.Opens

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable (K : Type u) [Field K]

local notation "𝒢" => homogeneousSubmodule (Fin 4) K
local notation "Pₖ" => AlgebraicGeometry.Proj 𝒢

/-- The original four coordinate opens cover the projective source. -/
theorem polynomialProjective_basicOpen_iSup :
    ⨆ a : Fin 4, Proj.basicOpen 𝒢 (X a) = ⊤ := by
  have hgen : Algebra.adjoin (𝒢 0) (Set.range (X : Fin 4 → MvPolynomial (Fin 4) K)) = ⊤ := by
    let S := Algebra.adjoin (𝒢 0) (Set.range (X : Fin 4 → MvPolynomial (Fin 4) K))
    apply top_unique
    intro P hP
    clear hP
    induction P using MvPolynomial.induction_on with
    | C c => exact S.algebraMap_mem ⟨MvPolynomial.C c, isHomogeneous_C (Fin 4) c⟩
    | add P Q hP hQ => exact S.add_mem hP hQ
    | mul_X P i hP => exact S.mul_mem hP (Algebra.subset_adjoin ⟨i, rfl⟩)
  exact Proj.iSup_basicOpen_eq_top' 𝒢 (X : Fin 4 → MvPolynomial (Fin 4) K)
    (fun i => ⟨1, isHomogeneous_X (R := K) i⟩) hgen

/-- The zero homogeneous prime is the original projective generic point. -/
noncomputable def polynomialProjectiveGenericPoint : ProjectiveSpectrum 𝒢 where
  asHomogeneousIdeal := ⊥
  isPrime := inferInstanceAs (⊥ : Ideal (MvPolynomial (Fin 4) K)).IsPrime
  not_irrelevant_le := by
    intro hle
    have hx := hle (HomogeneousIdeal.mem_irrelevant_of_mem _ (show 0 < (1 : ℕ) by omega)
      (isHomogeneous_X (R := K) (0 : Fin 4)))
    change X (0 : Fin 4) ∈ (⊥ : Ideal (MvPolynomial (Fin 4) K)) at hx
    exact X_ne_zero (0 : Fin 4) (Ideal.mem_bot.mp hx)

/-- This point has dense closure in the actual projective scheme. -/
theorem polynomialProjectiveGenericPoint_isGeneric :
    IsGenericPoint (polynomialProjectiveGenericPoint K : Pₖ) Set.univ := by
  change closure {polynomialProjectiveGenericPoint K} = Set.univ
  rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    ProjectiveSpectrum.vanishingIdeal_singleton]
  exact ProjectiveSpectrum.zeroLocus_bot _

/-- Every actual projective source stalk is a domain, using its
original affine section ring and the affine stalk localization. -/
theorem polynomialProjective_stalk_isDomain (x : Pₖ) : IsDomain ((Pₖ).presheaf.stalk x) := by
  obtain ⟨a, ha⟩ := mem_iSup.mp ((polynomialProjective_basicOpen_iSup K).ge
    (show x ∈ ⊤ from trivial))
  let U : (Pₖ).affineOpens := ⟨Proj.basicOpen 𝒢 (X a),
    Proj.isAffineOpen_basicOpen 𝒢 (X a) (isHomogeneous_X (R := K) a) (by omega)⟩
  let xU : U.1 := ⟨x, ha⟩
  let e := originalProjectiveAffineSectionEquiv (K := K) a
  let : IsDomain Γ(Pₖ, U.1) := Function.Injective.isDomain e.toRingHom e.injective
  let : Algebra Γ(Pₖ, U.1) ((Pₖ).presheaf.stalk x) :=
    (Pₖ).presheaf.algebra_section_stalk xU
  let : IsLocalization.AtPrime ((Pₖ).presheaf.stalk x) (U.2.primeIdealOf xU).asIdeal :=
    U.2.isLocalization_stalk xU
  let es := (IsLocalization.algEquiv (U.2.primeIdealOf xU).asIdeal.primeCompl
    ((Pₖ).presheaf.stalk x) (Localization.AtPrime (U.2.primeIdealOf xU).asIdeal)).toRingEquiv
  exact Function.Injective.isDomain es.toRingHom es.injective

/-- The actual original projective source is integral. -/
theorem polynomialProjective_isIntegral : IsIntegral Pₖ := by
  let : IrreducibleSpace Pₖ := (irreducibleSpace_def Pₖ).mpr
    (polynomialProjectiveGenericPoint_isGeneric K).isIrreducible
  let (x : Pₖ) : IsDomain ((Pₖ).presheaf.stalk x) := polynomialProjective_stalk_isDomain K x
  let : AlgebraicGeometry.IsReduced Pₖ := isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The original projective source is locally Noetherian over its field. -/
theorem polynomialProjective_isLocallyNoetherian : IsLocallyNoetherian Pₖ := by
  let : IsProper (polynomialProjectiveToBase K) := polynomialProjectiveToBase_isProper K
  exact LocallyOfFiniteType.isLocallyNoetherian (polynomialProjectiveToBase K)

end DimensionFourDependence
