import DimensionFourDependence.SegreRulingLocalTangentModel

/-! # Constructing residue tangent nilpotence from the original generic Jacobian -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 3000000

/-- The exact two proportional output rows in the ruling-preserving
source chart; these are the expressions differentiated in Lemma 5.2. -/
def segreRulingLocalOutputRows {R : Type*} [CommRing R]
    (j : ℕ) (π t a f g : R) : Fin 4 → R :=
  ![π ^ j * f, π ^ j * g, (t + π * a) * π ^ j * f, (t + π * a) * π ^ j * g]

/-- The local chart Jacobian is derived from the exact output identity
and the coordinate derivations. Its product and power terms are not
supplied as independent derivative assumptions. -/
theorem segre_ruling_local_output_jacobian_of_coordinate_derivations
    {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (δ : Fin 4 → Derivation K R R) (j : ℕ) (π t a f g : R)
    (hπ : ∀ i, δ i π = if i = 3 then 1 else 0)
    (ht : ∀ i, δ i t = if i = 2 then 1 else 0) :
    (Matrix.of fun r i => δ i (segreRulingLocalOutputRows j π t a f g r)) =
      segreRulingLocalOutputJacobian j π t a f g
        (fun i => δ i f) (fun i => δ i g) (fun i => δ i a) := by
  ext r i
  fin_cases r <;> fin_cases i <;>
    simp [segreRulingLocalOutputRows, segreRulingLocalOutputJacobian,
      Derivation.leibniz, Derivation.leibniz_pow, hπ, ht, nsmul_eq_mul, smul_eq_mul] <;> ring

/-- The source tangent-lattice frame is faithful over the actual generic
field, using only the nonzero uniformizer there. -/
theorem segre_ruling_source_tangent_frame_injective
    {F : Type*} [Field F] (t π : F) (hπ : π ≠ 0) :
    Function.Injective (segreRulingSourceTangentFrame t π).toLin' := by
  let Q : Matrix (Fin 4) (Fin 4) F :=
    !![1, 0, 0, 0; 0, 1, 0, 0; -t / π, 0, π⁻¹, 0; 0, -t / π, 0, π⁻¹]
  have hQP : Q * segreRulingSourceTangentFrame t π = 1 := by
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [Q, segreRulingSourceTangentFrame, Matrix.mul_apply, Fin.sum_univ_succ, hπ,
        div_eq_mul_inv] <;> ring
  have hleft : Function.LeftInverse (fun v => Q *ᵥ v) (segreRulingSourceTangentFrame t π).toLin' := by
    intro v
    change Q *ᵥ (segreRulingSourceTangentFrame t π *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
  exact hleft.injective

/-- A nilpotent original generic Jacobian and its exact chart chain
rule construct nilpotence of the full residue tangent matrix. The
normalized regular matrix, its faithful source frame and its residue
specialization are all constructed internally. -/
theorem segre_ruling_generic_jacobian_constructs_residue_tangent_nilpotence
    {O F κ : Type*} [CommRing O] [Field F] [CommRing κ]
    (φ : O →+* F) (hφ : Function.Injective φ) (σ : O →+* κ)
    (j : ℕ) (π t z s a f g : O) (df dg da : Fin 4 → O)
    (hπF : φ π ≠ 0) (hπκ : σ π = 0)
    (J : Matrix (Fin 4) (Fin 4) F) (hJ : IsNilpotent J)
    (hchain : J * segreRulingSourceTangentFrame (φ t) (φ π) =
      segreRulingLocalOutputJacobian j (φ π) (φ t) (φ a) (φ f) (φ g)
        (fun i => φ (df i)) (fun i => φ (dg i)) (fun i => φ (da i)) *
      segreRulingChartVariationMatrix (φ π) (φ z) (φ s)) :
    IsNilpotent (segreRulingChartTangentMatrix (j : κ) (σ f) (σ g)
      (σ (df 0)) (σ (df 1)) (σ (dg 0)) (σ (dg 1))
      (σ a) (σ (da 0)) (σ (da 1)) (σ z) (σ s)) := by
  let B := segreRulingSourceTangentFrame (φ t) (φ π)
  let T := segreRulingLocalTangentMatrix (j : F) (φ π) (φ z) (φ s) (φ a) (φ f) (φ g)
    (fun i => φ (df i)) (fun i => φ (dg i)) (fun i => φ (da i))
  have haction : J * B = (φ π) ^ j • (B * T) :=
    hchain.trans (segre_ruling_local_jacobian_tangent_identity
      j (φ π) (φ t) (φ z) (φ s) (φ a) (φ f) (φ g)
        (fun i => φ (df i)) (fun i => φ (dg i)) (fun i => φ (da i)))
  have hcompat : B * T = (((φ π) ^ j)⁻¹ • J) * B := by
    rw [Matrix.smul_mul, haction, smul_smul, inv_mul_cancel₀ (pow_ne_zero j hπF), one_smul]
  have hT := matrix_isNilpotent_of_injective_intertwiner _ T B
    (segre_ruling_source_tangent_frame_injective _ _ hπF) hcompat (hJ.smul _)
  have hmap : IsNilpotent ((segreRulingLocalTangentMatrix (j : O) π z s a f g df dg da).map φ) := by
    rw [segreRulingLocalTangentMatrix_map, map_natCast]
    exact hT
  have hres := matrix_isNilpotent_specialization_of_generic φ hφ σ _ hmap
  rw [segre_ruling_local_tangent_specialization σ _ π z s a f g df dg da hπκ] at hres
  simpa only [map_natCast] using hres

end DimensionFourDependence
