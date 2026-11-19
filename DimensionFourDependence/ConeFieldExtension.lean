import DimensionFourDependence.ComponentGenericPoint

/-! # Affine scalar-extension relations imply projective closure relations -/

namespace DimensionFourDependence

open MvPolynomial

variable {L E F G σ : Type*} [Field L] [Field E] [Field F] [Field G]
    [Algebra L E] [Algebra L F] [Algebra E G] [Algebra L G] [IsScalarTower L E G]

/-- Coefficient extension commutes with evaluation through a scalar tower. -/
theorem aeval_map_coefficients (z : σ → G) (p : MvPolynomial σ L) :
    aeval z (MvPolynomial.map (algebraMap L E) p) = aeval z p := by
  change MvPolynomial.eval₂ (algebraMap E G) z (MvPolynomial.map (algebraMap L E) p) =
    MvPolynomial.eval₂ (algebraMap L G) z p
  rw [MvPolynomial.eval₂_map, ← IsScalarTower.algebraMap_eq L E G]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A point of the scalar-extended affine fiber has its projective closure
inside the scalar extension of the original projective closure. -/
theorem projectiveConeIdeal_extended_le {n : ℕ} (x : Fin n → F) (z : Fin n → G)
    (hrel : extendCoefficientIdeal E (fiberVanishingIdeal (L := L) x) ≤
      fiberVanishingIdeal (L := E) z) :
    extendCoefficientIdeal E (projectiveConeIdeal (L := L) x) ≤ projectiveConeIdeal (L := E) z := by
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists
    (𝒜 := homogeneousSubmodule (Option (Fin n)) L) (I := projectiveConeIdeal (L := L) x)).mp
      (projectiveConeIdeal_isHomogeneous x)
  unfold extendCoefficientIdeal
  rw [hS, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨p, ⟨s, hs, rfl⟩, rfl⟩
  obtain ⟨d, hd⟩ := s.property
  have hf : (s : MvPolynomial (Option (Fin n)) L).IsHomogeneous d := hd
  have hm : (s : MvPolynomial (Option (Fin n)) L) ∈ projectiveConeIdeal (L := L) x := by
    rw [hS]
    exact Ideal.subset_span ⟨s, hs, rfl⟩
  have ha : projectiveDehomogenize (s : MvPolynomial (Option (Fin n)) L) ∈
      fiberVanishingIdeal (L := L) x := by
    change aeval x (projectiveDehomogenize (s : MvPolynomial (Option (Fin n)) L)) = 0
    rw [← aeval_projectiveDehomogenize]
    exact (projectiveConeIdeal_mem_of_isHomogeneous x hf).mp hm
  have hz := hrel (Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap L E)) ha)
  change aeval z (MvPolynomial.map (algebraMap L E)
    (projectiveDehomogenize (s : MvPolynomial (Option (Fin n)) L))) = 0 at hz
  rw [aeval_map_coefficients] at hz
  apply (projectiveConeIdeal_mem_of_isHomogeneous z (hf.map (algebraMap L E))).mpr
  rw [aeval_map_coefficients, aeval_projectiveDehomogenize]
  exact hz

end DimensionFourDependence
