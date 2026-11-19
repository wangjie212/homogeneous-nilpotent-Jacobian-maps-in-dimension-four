import DimensionFourDependence.SegreOriginalEulerWeights

/-! # The actual original Euler weights survive in the ruling residue field -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "X₀" => rationalCoordinate (K := K) (n := 4)
local notation "E₀" => sourceEuler (K := K) (n := 4)
local notation "D₀" => segreOriginalSourceChartDerivation (K := K)

/-- A regular original source Euler eigenvalue descends through the
faithful source realization and then to the actual uniformizer residue.
The vanished transverse term is retained until the residue is taken. -/
theorem segre_original_euler_weight_constructs_residue_weight
    {O κ : Type*} [CommRing O] [CommRing κ]
    (φ : O →+* F₀) (hφ : Function.Injective φ) (σ : O →+* κ)
    (x y π v α : O) (dv : Fin 4 → O)
    (hx : φ x = (X₀) 0) (hy : φ y = (X₀) 1)
    (hπ : φ π = segreOriginalSourceUniformizer (K := K)) (hπκ : σ π = 0)
    (hdv : ∀ i, φ (dv i) = (D₀) i (φ v))
    (hweight : (E₀) (φ v) = φ α * φ v) :
    σ x * σ (dv 0) + σ y * σ (dv 1) = σ α * σ v := by
  have hO : x * dv 0 + y * dv 1 + π * dv 3 = α * v := by
    apply hφ
    simp only [map_add, map_mul]
    rw [hx, hy, hπ, hdv 0, hdv 1, hdv 3]
    have he := congrArg (fun D : Derivation K F₀ F₀ => D (φ v))
      (segre_original_source_euler_decomposition (K := K))
    simp only [Derivation.add_apply, Derivation.smul_apply, smul_eq_mul] at he
    exact he.symm.trans hweight
  have hres := congrArg σ hO
  simpa only [map_add, map_mul, hπκ, zero_mul, add_zero] using hres

/-- The exact original homogeneous map supplies all three residue Euler
identities needed to construct the normalized row and slope profiles. -/
theorem segre_original_regular_output_constructs_residue_euler_weights
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (hind : ¬ComponentsDependent H)
    {O κ : Type*} [CommRing O] [CommRing κ]
    (φ : O →+* F₀) (hφ : Function.Injective φ) (σ : O →+* κ)
    (j : ℕ) (x y π t a f g : O) (df dg da : Fin 4 → O)
    (hx : φ x = (X₀) 0) (hy : φ y = (X₀) 1)
    (hπ : φ π = segreOriginalSourceUniformizer (K := K))
    (ht : φ t = segreOriginalSourceRulingParameter (K := K)) (hπκ : σ π = 0)
    (hrows : ∀ r, algebraMap (MvPolynomial (Fin 4) K) F₀ (H r) =
      segreRulingLocalOutputRows j (φ π) (φ t) (φ a) (φ f) (φ g) r)
    (hdf : ∀ i, φ (df i) = (D₀) i (φ f))
    (hdg : ∀ i, φ (dg i) = (D₀) i (φ g))
    (hda : ∀ i, φ (da i) = (D₀) i (φ a)) :
    (σ x * σ (df 0) + σ y * σ (df 1) = ((d : κ) - (j : κ)) * σ f) ∧
      (σ x * σ (dg 0) + σ y * σ (dg 1) = ((d : κ) - (j : κ)) * σ g) ∧
      (σ x * σ (da 0) + σ y * σ (da 1) = -σ a) := by
  have hrows' : ∀ r, algebraMap (MvPolynomial (Fin 4) K) F₀ (H r) =
      segreRulingLocalOutputRows j (segreOriginalSourceUniformizer (K := K))
        (segreOriginalSourceRulingParameter (K := K)) (φ a) (φ f) (φ g) r := by
    intro r
    simpa only [hπ, ht] using hrows r
  obtain ⟨hfE, hgE, haE⟩ := segre_original_output_rows_construct_euler_weights H hH hind j (φ a) (φ f) (φ g) hrows'
  have hfW : (E₀) (φ f) = φ ((d : O) - (j : O)) * φ f := by simpa only [map_sub, map_natCast] using hfE
  have hgW : (E₀) (φ g) = φ ((d : O) - (j : O)) * φ g := by simpa only [map_sub, map_natCast] using hgE
  have haW : (E₀) (φ a) = φ (-1 : O) * φ a := by simpa only [map_neg, map_one, neg_one_mul] using haE
  refine ⟨?_, ?_, ?_⟩
  · simpa only [map_sub, map_natCast] using segre_original_euler_weight_constructs_residue_weight
      φ hφ σ x y π f ((d : O) - (j : O)) df hx hy hπ hπκ hdf hfW
  · simpa only [map_sub, map_natCast] using segre_original_euler_weight_constructs_residue_weight
      φ hφ σ x y π g ((d : O) - (j : O)) dg hx hy hπ hπκ hdg hgW
  · simpa only [map_neg, map_one, neg_one_mul] using segre_original_euler_weight_constructs_residue_weight
      φ hφ σ x y π a (-1 : O) da hx hy hπ hπκ hda haW

end DimensionFourDependence
