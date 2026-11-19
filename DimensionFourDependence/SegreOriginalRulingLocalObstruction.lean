import DimensionFourDependence.SegreOriginalLocalOutputReduction
import DimensionFourDependence.SegreOriginalResidueEuler
import DimensionFourDependence.SegreOriginalResidueCoordinates
import DimensionFourDependence.SegreEulerTangentObstruction
import DimensionFourDependence.SegrePrimitiveDegreeBound

/-! # The complete ruling differential contradiction for a faithful original local model -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "X₀" => rationalCoordinate (K := K) (n := 4)
local notation "D₀" => segreOriginalSourceChartDerivation (K := K)

/-- The original homogeneous nilpotent map contradicts a regular
ruling-preserving source model with nonzero ruling dominance. The source
chain rule, residue tangent nilpotence, residue coordinate values, Euler
weights, homogeneous profiles and all reduced matrix contradictions are
constructed internally from this exact original local model. -/
theorem segre_original_regular_ruling_model_impossible
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hind : ¬ComponentsDependent H)
    {O κ : Type*} [CommRing O] [Field κ] [Algebra K O] [Algebra K κ]
    (φ : O →+* F₀) (hφ : Function.Injective φ) (σ : O →+* κ)
    (D : Fin 4 → Derivation K O O) (hD : ∀ i v, φ (D i v) = (D₀) i (φ v))
    (Dx Dy : Derivation K κ κ)
    (hDx : ∀ v, Dx (σ v) = σ (D 0 v)) (hDy : ∀ v, Dy (σ v) = σ (D 1 v))
    (j : ℕ) (x y π t z s a f g : O)
    (hx : φ x = (X₀) 0) (hy : φ y = (X₀) 1)
    (hπ : φ π = segreOriginalSourceUniformizer (K := K))
    (ht : φ t = segreOriginalSourceRulingParameter (K := K))
    (hz : φ z = ((X₀) 0)⁻¹) (hs : φ s = (X₀) 1 / (X₀) 0) (hπκ : σ π = 0)
    (hrows : ∀ r, algebraMap (MvPolynomial (Fin 4) K) F₀ (H r) =
      segreRulingLocalOutputRows j (φ π) (φ t) (φ a) (φ f) (φ g) r)
    (hdegree : 2 * j < d)
    (hdom : σ f * Dy (σ g) - σ g * Dy (σ f) ≠ 0) : False := by
  letI : CharZero κ := charZero_of_injective_algebraMap (algebraMap K κ).injective
  have hres := segre_original_regular_output_constructs_residue_tangent_nilpotence H hN
    φ hφ σ j π t z s a f g (fun i => D i f) (fun i => D i g) (fun i => D i a)
      hπ ht hz hs hπκ hrows (fun i => hD i f) (fun i => hD i g) (fun i => hD i a)
  obtain ⟨hfE, hgE, haE⟩ := segre_original_regular_output_constructs_residue_euler_weights H hH hind
    φ hφ σ j x y π t a f g (fun i => D i f) (fun i => D i g) (fun i => D i a)
      hx hy hπ ht hπκ hrows (fun i => hD i f) (fun i => hD i g) (fun i => hD i a)
  obtain ⟨hxκ, hzκ, hsκ⟩ := segre_original_regular_coordinates_construct_residue_ratios φ hφ σ x y z s hx hy hz hs
  obtain ⟨_hxx, _hxy, hyx, hyy⟩ := segre_original_regular_derivations_construct_residue_coordinates
    φ hφ σ D hD Dx Dy hDx hDy x y hx hy
  change σ x * σ (D 0 f) + σ y * σ (D 1 f) = _ at hfE
  change σ x * σ (D 0 g) + σ y * σ (D 1 g) = _ at hgE
  change σ x * σ (D 0 a) + σ y * σ (D 1 a) = _ at haE
  rw [← hDx f, ← hDy f] at hfE
  rw [← hDx g, ← hDy g] at hgE
  rw [← hDx a, ← hDy a] at haE
  change IsNilpotent (segreRulingChartTangentMatrix (j : κ) (σ f) (σ g)
    (σ (D 0 f)) (σ (D 1 f)) (σ (D 0 g)) (σ (D 1 g))
    (σ a) (σ (D 0 a)) (σ (D 1 a)) (σ z) (σ s)) at hres
  rw [← hDx f, ← hDy f, ← hDx g, ← hDy g, ← hDx a, ← hDy a, hzκ, hsκ] at hres
  exact segre_ruling_euler_chart_not_nilpotent Dx Dy (σ x) (σ y) (σ f) (σ g) (σ a)
    hxκ hyx hyy d j hdegree hfE hgE haE hdom hres

end DimensionFourDependence
