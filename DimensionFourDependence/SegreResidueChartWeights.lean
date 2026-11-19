import DimensionFourDependence.SegreCanonicalResidueExclusion

/-! # Residue coordinate values and Euler weights from the original source chart -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "X₀" => rationalCoordinate (K := K) (n := 4)
local notation "D₀" => segreOriginalSourceChartDerivation (K := K)

variable {O : Type*} [CommRing O] [IsLocalRing O] [Algebra K O]
local notation "κ₀" => IsLocalRing.ResidueField O
local notation "σ₀" => IsLocalRing.residue O

/-- The actual source realization fixes the coordinate values of the
two residue derivatives and their radial Euler combination. -/
theorem segre_regular_chart_constructs_residue_coordinate_values
    (φ : O →+* F₀) (hφ : Function.Injective φ)
    (D : Fin 4 → Derivation K O O) (hD : ∀ i v, φ (D i v) = (D₀) i (φ v))
    (Dx Dy : Derivation K κ₀ κ₀)
    (hDx : ∀ v, Dx ((σ₀) v) = (σ₀) (D 0 v))
    (hDy : ∀ v, Dy ((σ₀) v) = (σ₀) (D 1 v))
    (x y t : O) (hx : φ x = (X₀) 0) (hy : φ y = (X₀) 1)
    (ht : φ t = segreOriginalSourceRulingParameter (K := K)) :
    Dy ((σ₀) x) = 0 ∧ Dy ((σ₀) y) = 1 ∧ Dy ((σ₀) t) = 0 ∧
      ((σ₀) x • Dx + (σ₀) y • Dy) ((σ₀) x) = (σ₀) x ∧
      ((σ₀) x • Dx + (σ₀) y • Dy) ((σ₀) y) = (σ₀) y := by
  have h0x : D 0 x = 1 := by
    apply hφ
    simp [hD, hx, segre_original_source_chart_derivation_coordinate, segreSourceChartMatrix]
  have h1x : D 1 x = 0 := by
    apply hφ
    simp [hD, hx, segre_original_source_chart_derivation_coordinate, segreSourceChartMatrix]
  have h0y : D 0 y = 0 := by
    apply hφ
    simp [hD, hy, segre_original_source_chart_derivation_coordinate, segreSourceChartMatrix]
  have h1y : D 1 y = 1 := by
    apply hφ
    simp [hD, hy, segre_original_source_chart_derivation_coordinate, segreSourceChartMatrix]
  have h1t : D 1 t = 0 := by
    apply hφ
    simp [hD, ht, segre_original_source_chart_derivation_parameter]
  simp [Derivation.add_apply, Derivation.smul_apply, smul_eq_mul, hDx, hDy, h0x, h1x, h0y, h1y, h1t]

/-- Homogeneity of an original polynomial gives its exact residue Euler
weight, using the constructed regular chart and its residue derivatives. -/
theorem segre_original_homogeneous_polynomial_residue_euler_weight
    (φ : O →+* F₀) (hφ : Function.Injective φ)
    (D : Fin 4 → Derivation K O O) (hD : ∀ i v, φ (D i v) = (D₀) i (φ v))
    (Dx Dy : Derivation K κ₀ κ₀)
    (hDx : ∀ v, Dx ((σ₀) v) = (σ₀) (D 0 v))
    (hDy : ∀ v, Dy ((σ₀) v) = (σ₀) (D 1 v))
    (x y π w : O) (hx : φ x = (X₀) 0) (hy : φ y = (X₀) 1)
    (hπ : φ π = segreOriginalSourceUniformizer (K := K)) (hπκ : (σ₀) π = 0)
    (P : MvPolynomial (Fin 4) K) {m : ℕ} (hP : P.IsHomogeneous m)
    (hw : φ w = algebraMap (MvPolynomial (Fin 4) K) F₀ P) :
    ((σ₀) x • Dx + (σ₀) y • Dy) ((σ₀) w) = (m : κ₀) * (σ₀) w := by
  have he := segre_original_euler_weight_constructs_residue_weight φ hφ (σ₀)
    x y π w (m : O) (fun i => D i w) hx hy hπ hπκ (fun i => hD i w) (by
      rw [hw, map_natCast]
      exact sourceEuler_homogeneous P hP)
  simpa only [Derivation.add_apply, Derivation.smul_apply, smul_eq_mul, hDx, hDy, map_natCast] using he

end DimensionFourDependence
