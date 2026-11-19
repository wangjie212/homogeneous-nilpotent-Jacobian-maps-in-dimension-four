import DimensionFourDependence.SegreOriginalSourceChart

/-! # The original polynomial map constructs the local residue tangent reduction -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]

local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "X₀" => rationalCoordinate (K := K) (n := 4)
local notation "D₀" => segreOriginalSourceChartDerivation (K := K)

/-- Exact regular realizations of the original ruling-preserving output
rows and their chart derivatives construct nilpotence of the residue
matrix directly from the original nilpotent polynomial Jacobian. The
original source frame and chart chain rule are derived internally. -/
theorem segre_original_regular_output_constructs_residue_tangent_nilpotence
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    {O κ : Type*} [CommRing O] [CommRing κ]
    (φ : O →+* F₀) (hφ : Function.Injective φ) (σ : O →+* κ)
    (j : ℕ) (π t z s a f g : O) (df dg da : Fin 4 → O)
    (hπ : φ π = segreOriginalSourceUniformizer (K := K))
    (ht : φ t = segreOriginalSourceRulingParameter (K := K))
    (hz : φ z = ((X₀) 0)⁻¹) (hs : φ s = (X₀) 1 / (X₀) 0)
    (hπκ : σ π = 0)
    (hrows : ∀ r, algebraMap (MvPolynomial (Fin 4) K) F₀ (H r) =
      segreRulingLocalOutputRows j (φ π) (φ t) (φ a) (φ f) (φ g) r)
    (hdf : ∀ i, φ (df i) = (D₀) i (φ f))
    (hdg : ∀ i, φ (dg i) = (D₀) i (φ g))
    (hda : ∀ i, φ (da i) = (D₀) i (φ a)) :
    IsNilpotent (segreRulingChartTangentMatrix (j : κ) (σ f) (σ g)
      (σ (df 0)) (σ (df 1)) (σ (dg 0)) (σ (dg 1))
      (σ a) (σ (da 0)) (σ (da 1)) (σ z) (σ s)) := by
  have hπD (i : Fin 4) : (D₀) i (φ π) = if i = 3 then 1 else 0 := by
    rw [hπ]
    exact segre_original_source_chart_derivation_uniformizer i
  have htD (i : Fin 4) : (D₀) i (φ t) = if i = 2 then 1 else 0 := by
    rw [ht]
    exact segre_original_source_chart_derivation_parameter i
  have hrowD : (Matrix.of fun r i => (D₀) i
      (algebraMap (MvPolynomial (Fin 4) K) F₀ (H r))) =
      Matrix.of fun r i => (D₀) i (segreRulingLocalOutputRows j (φ π) (φ t) (φ a) (φ f) (φ g) r) := by
    ext r i
    exact congrArg ((D₀) i) (hrows r)
  have hJac : (Matrix.of fun r i => (D₀) i
      (algebraMap (MvPolynomial (Fin 4) K) F₀ (H r))) =
      segreRulingLocalOutputJacobian j (φ π) (φ t) (φ a) (φ f) (φ g)
        (fun i => φ (df i)) (fun i => φ (dg i)) (fun i => φ (da i)) := by
    rw [hrowD, segre_ruling_local_output_jacobian_of_coordinate_derivations
      (D₀) j (φ π) (φ t) (φ a) (φ f) (φ g) hπD htD]
    rw [show (fun i => (D₀) i (φ f)) = (fun i => φ (df i)) from funext (fun i => (hdf i).symm),
      show (fun i => (D₀) i (φ g)) = (fun i => φ (dg i)) from funext (fun i => (hdg i).symm),
      show (fun i => (D₀) i (φ a)) = (fun i => φ (da i)) from funext (fun i => (hda i).symm)]
  have hchain := segre_original_source_jacobian_tangent_chain_rule H
  rw [← ht, ← hπ, ← hz, ← hs, hJac] at hchain
  have hπF : φ π ≠ 0 := by
    rw [hπ]
    exact segre_original_source_uniformizer_ne_zero
  exact segre_ruling_generic_jacobian_constructs_residue_tangent_nilpotence
    φ hφ σ j π t z s a f g df dg da hπF hπκ _
      (hN.map (algebraMap (MvPolynomial (Fin 4) K) F₀).mapMatrix) hchain

end DimensionFourDependence
