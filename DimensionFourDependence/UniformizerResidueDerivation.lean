import DimensionFourDependence.Defs

/-! # A uniformizer-preserving local derivation constructs its residue derivation -/

namespace DimensionFourDependence

open MvPolynomial

variable {K O : Type*} [Field K] [CommRing O] [IsLocalRing O] [Algebra K O]

/-- Vanishing on a chosen generator of the actual local maximal ideal
forces a derivation to preserve the entire residue kernel. -/
theorem uniformizer_derivation_preserves_residue_kernel
    (D : Derivation K O O) (π : O)
    (hmax : IsLocalRing.maximalIdeal O = Ideal.span {π}) (hDπ : D π = 0)
    (v : O) (hv : IsLocalRing.residue O v = 0) : IsLocalRing.residue O (D v) = 0 := by
  have hmem := (IsLocalRing.residue_eq_zero_iff v).mp hv
  rw [hmax] at hmem
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hmem
  have hπres : IsLocalRing.residue O π = 0 := by
    apply (IsLocalRing.residue_eq_zero_iff π).mpr
    rw [hmax]
    exact Ideal.subset_span (by simp)
  rw [hb, Derivation.leibniz, hDπ]
  simp [smul_eq_mul, hπres]

/-- The derivation on the actual local residue field, constructed by
surjective descent from the original local operator. -/
noncomputable def uniformizerResidueDerivation
    (D : Derivation K O O) (π : O)
    (hmax : IsLocalRing.maximalIdeal O = Ideal.span {π}) (hDπ : D π = 0) :
    Derivation K (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O) :=
  Derivation.liftOfSurjective
    (f := IsScalarTower.toAlgHom K O (IsLocalRing.ResidueField O))
    (IsLocalRing.residue_surjective (R := O))
    (uniformizer_derivation_preserves_residue_kernel D π hmax hDπ)

/-- The constructed residue derivative retains the value of every
original regular element, with no chosen representatives in its API. -/
theorem uniformizerResidueDerivation_residue
    (D : Derivation K O O) (π : O)
    (hmax : IsLocalRing.maximalIdeal O = Ideal.span {π}) (hDπ : D π = 0) (v : O) :
    uniformizerResidueDerivation D π hmax hDπ (IsLocalRing.residue O v) =
      IsLocalRing.residue O (D v) :=
  Derivation.liftOfSurjective_apply
    (f := IsScalarTower.toAlgHom K O (IsLocalRing.ResidueField O))
    (IsLocalRing.residue_surjective (R := O))
    (uniformizer_derivation_preserves_residue_kernel D π hmax hDπ) v

end DimensionFourDependence
