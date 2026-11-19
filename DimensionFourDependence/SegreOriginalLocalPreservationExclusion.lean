import DimensionFourDependence.SegreOriginalRulingLocalObstruction
import DimensionFourDependence.SegreRegularRulingRows

/-! # Original common-factor and residue-preservation data construct the Segre contradiction -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "X₀" => rationalCoordinate (K := K) (n := 4)
local notation "D₀" => segreOriginalSourceChartDerivation (K := K)

/-- The original Segre image identity and an actual regular local
ruling-preserving realization construct the slope formula and its
primitive order bound. The whole local differential contradiction is
then derived from the original homogeneous nilpotent map, without
supplied slope, Euler weights, profiles, numeric degree bound, transformed
Jacobian or reduced nilpotence. -/
theorem segre_original_local_ruling_preservation_excluded
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (G : MvPolynomial (Fin 4) K) (P : Fin 4 → MvPolynomial (Fin 4) K) (c : ℕ)
    (hG : G ≠ 0) (hGh : G.IsHomogeneous c) (hP : IsHomogMap P (d - c))
    (hHP : H = fun i => G * P i)
    {O : Type*} [CommRing O] [IsLocalRing O] [Algebra K O]
    (φ : O →+* F₀) (hφ : Function.Injective φ)
    (D : Fin 4 → Derivation K O O) (hD : ∀ i v, φ (D i v) = (D₀) i (φ v))
    (Dx Dy : Derivation K (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O))
    (hDx : ∀ v, Dx (IsLocalRing.residue O v) = IsLocalRing.residue O (D 0 v))
    (hDy : ∀ v, Dy (IsLocalRing.residue O v) = IsLocalRing.residue O (D 1 v))
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
    (hdom : IsLocalRing.residue O (p 0) * Dy (IsLocalRing.residue O (p 1)) -
      IsLocalRing.residue O (p 1) * Dy (IsLocalRing.residue O (p 0)) ≠ 0) : False := by
  letI : IsDomain O := Function.Injective.isDomain φ hφ
  have hπO : π ≠ 0 := by
    intro he
    apply segre_original_source_uniformizer_ne_zero (K := K)
    rw [← hπ, he, map_zero]
  have hdet : h 0 * h 3 - h 1 * h 2 = 0 := by
    apply hφ
    simp only [map_sub, map_mul, map_zero, houtputs]
    have he := congrArg (algebraMap (MvPolynomial (Fin 4) K) F₀) hSegre
    simpa only [map_sub, map_mul, map_zero] using he
  obtain ⟨a, hrowsO⟩ := segre_regular_factored_outputs_construct_ruling_formula
    j π t hπO h p hfactor u hfirst hmax hpres hdet
  have hrows : ∀ r, algebraMap (MvPolynomial (Fin 4) K) F₀ (H r) =
      segreRulingLocalOutputRows j (φ π) (φ t) (φ a) (φ (p 0)) (φ (p 1)) r := by
    intro r
    calc
      _ = φ (h r) := (houtputs r).symm
      _ = φ (segreRulingLocalOutputRows j π t a (p 0) (p 1) r) := congrArg φ (congrFun hrowsO r)
      _ = _ := by fin_cases r <;> simp [segreRulingLocalOutputRows]
  have hprimitive := primitive_map_degree_ge_two_of_actual_image_relation H hind I G hG P hP hHP
  have hdegree := segre_determinant_power_common_factor_degree_bound G hG hGh hprimitive j hdiv
  have hπκ : IsLocalRing.residue O π = 0 := by
    apply (IsLocalRing.residue_eq_zero_iff π).mpr
    rw [hmax]
    exact Ideal.subset_span (by simp)
  exact segre_original_regular_ruling_model_impossible H hH hN hind
    φ hφ (IsLocalRing.residue O) D hD Dx Dy hDx hDy
      j x y π t z s a (p 0) (p 1) hx hy hπ ht hz hs hπκ hrows hdegree hdom

end DimensionFourDependence
