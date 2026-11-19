import DimensionFourDependence.SegreOriginalLocalPreservationExclusion
import DimensionFourDependence.UniformizerResidueDerivation

/-! # The original regular chart constructs the residue derivations used in the exclusion -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "X₀" => rationalCoordinate (K := K) (n := 4)
local notation "D₀" => segreOriginalSourceChartDerivation (K := K)

/-- Compatible regular realizations of the original source chart
operators construct both residue-plane derivatives and their values on
every regular element. Their residue compatibility is not supplied. -/
theorem segre_regular_source_derivations_construct_residue_operators
    {O : Type*} [CommRing O] [IsLocalRing O] [Algebra K O]
    (φ : O →+* F₀) (hφ : Function.Injective φ)
    (D : Fin 4 → Derivation K O O) (hD : ∀ i v, φ (D i v) = (D₀) i (φ v))
    (π : O) (hπ : φ π = segreOriginalSourceUniformizer (K := K))
    (hmax : IsLocalRing.maximalIdeal O = Ideal.span {π}) :
    ∃ Dx Dy : Derivation K (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O),
      (∀ v, Dx (IsLocalRing.residue O v) = IsLocalRing.residue O (D 0 v)) ∧
      (∀ v, Dy (IsLocalRing.residue O v) = IsLocalRing.residue O (D 1 v)) := by
  have hD0 : D 0 π = 0 := by
    apply hφ
    rw [hD, hπ, segre_original_source_chart_derivation_uniformizer]
    simp
  have hD1 : D 1 π = 0 := by
    apply hφ
    rw [hD, hπ, segre_original_source_chart_derivation_uniformizer]
    simp
  exact ⟨uniformizerResidueDerivation (D 0) π hmax hD0,
    uniformizerResidueDerivation (D 1) π hmax hD1,
    fun v => uniformizerResidueDerivation_residue (D 0) π hmax hD0 v,
    fun v => uniformizerResidueDerivation_residue (D 1) π hmax hD1 v⟩

/-- The actual original homogeneous map excludes a regular dominant
ruling-preserving source chart. Residue derivatives, the regular slope,
primitive degree bound, source and residue Euler identities, homogeneous
profiles and the complete differential matrix contradiction are all
constructed internally from the specified original regular chart. -/
theorem segre_original_regular_source_ruling_preservation_excluded
    [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (G : MvPolynomial (Fin 4) K) (P : Fin 4 → MvPolynomial (Fin 4) K) (c : ℕ)
    (hG : G ≠ 0) (hGh : G.IsHomogeneous c) (hP : IsHomogMap P (d - c))
    (hHP : H = fun i => G * P i)
    {O : Type*} [CommRing O] [IsLocalRing O] [Algebra K O]
    (φ : O →+* F₀) (hφ : Function.Injective φ)
    (D : Fin 4 → Derivation K O O) (hD : ∀ i v, φ (D i v) = (D₀) i (φ v))
    (j : ℕ) (x y π t z s : O) (h p : Fin 4 → O)
    (hx : φ x = (X₀) 0) (hy : φ y = (X₀) 1)
    (hπ : φ π = segreOriginalSourceUniformizer (K := K))
    (ht : φ t = segreOriginalSourceRulingParameter (K := K))
    (hz : φ z = ((X₀) 0)⁻¹) (hs : φ s = (X₀) 1 / (X₀) 0)
    (hmax : IsLocalRing.maximalIdeal O = Ideal.span {π})
    (houtputs : ∀ r, φ (h r) = algebraMap (MvPolynomial (Fin 4) K) F₀ (H r))
    (hfactor : ∀ r, h r = π ^ j * p r)
    (u : Oˣ) (hfirst : p 0 = (u : O))
    (hpres : IsLocalRing.residue O (p 2 * (↑u⁻¹ : O)) = IsLocalRing.residue O t)
    (hdiv : standardRulingPolynomial (F := K) ^ j ∣ G)
    (hdom : IsLocalRing.residue O (p 0) * IsLocalRing.residue O (D 1 (p 1)) -
      IsLocalRing.residue O (p 1) * IsLocalRing.residue O (D 1 (p 0)) ≠ 0) : False := by
  obtain ⟨Dx, Dy, hDx, hDy⟩ := segre_regular_source_derivations_construct_residue_operators φ hφ D hD π hπ hmax
  have hdom' : IsLocalRing.residue O (p 0) * Dy (IsLocalRing.residue O (p 1)) -
      IsLocalRing.residue O (p 1) * Dy (IsLocalRing.residue O (p 0)) ≠ 0 := by
    simpa only [hDy] using hdom
  exact segre_original_local_ruling_preservation_excluded H hH hN hind I hSegre
    G P c hG hGh hP hHP φ hφ D hD Dx Dy hDx hDy j x y π t z s h p
      hx hy hπ ht hz hs hmax houtputs hfactor u hfirst hpres hdiv hdom'

end DimensionFourDependence
