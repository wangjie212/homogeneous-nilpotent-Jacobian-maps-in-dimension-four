import DimensionFourDependence.SimplePoleTangentAction

/-! # The local simple-pole obstruction in Lemma 4.3

Integral tangent lifts, faithful fraction-space realization and residue
functional transport are constructed from the original matrix data.
-/

namespace DimensionFourDependence

open Matrix

variable {κ : Type*} [Field κ] {n : ℕ}

/-- Covectors with the same kernel on the actual tangent hyperplane
are proportional there. The scalar and its nonvanishing are derived. -/
theorem covectors_same_tangent_kernel_proportional
    (r b q : Fin n → κ)
    (hb : ∃ v : Fin n → κ, r ⬝ᵥ v = 0 ∧ b ⬝ᵥ v ≠ 0)
    (hker : ∀ v : Fin n → κ, r ⬝ᵥ v = 0 → (b ⬝ᵥ v = 0 ↔ q ⬝ᵥ v = 0)) :
    ∃ γ : κ, γ ≠ 0 ∧ ∀ v : Fin n → κ, r ⬝ᵥ v = 0 → q ⬝ᵥ v = γ * (b ⬝ᵥ v) := by
  obtain ⟨v₀, hv₀, hb₀⟩ := hb
  have hq₀ : q ⬝ᵥ v₀ ≠ 0 := fun hz => hb₀ ((hker v₀ hv₀).mpr hz)
  let γ := (q ⬝ᵥ v₀) / (b ⬝ᵥ v₀)
  refine ⟨γ, div_ne_zero hq₀ hb₀, ?_⟩
  intro v hv
  let a := (b ⬝ᵥ v) / (b ⬝ᵥ v₀)
  let u := v - a • v₀
  have hu : r ⬝ᵥ u = 0 := by simp only [u, dotProduct_sub, dotProduct_smul, hv, hv₀, smul_zero, sub_zero]
  have hbu : b ⬝ᵥ u = 0 := by
    simp only [u, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ hb₀).symm
  have hqu := (hker u hu).mp hbu
  simp only [u, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hqu
  rw [sub_eq_zero] at hqu
  rw [hqu]
  dsimp [a, γ]
  ring

variable {O F : Type*} [CommRing O] [Field F] [Algebra O F] [Algebra O κ]

/-- A simple-pole matrix with the parameter differential transport
and proportional tangent covectors cannot be nilpotent. The invariant
integral lattice, its endomorphism and nonzero residue functional are
constructed internally. -/
theorem simplePoleMatrix_not_isNilpotent_of_covector_transport
    (hinj : Function.Injective (algebraMap O F)) (hsurj : Function.Surjective (algebraMap O κ))
    (π m : O) (J : Matrix (Fin n) (Fin n) O) (P r s : Fin n → O)
    (hπF : algebraMap O F π ≠ 0)
    (hπκ : RingHom.ker (algebraMap O κ) = Ideal.span {π})
    (hP : (fun i => algebraMap O κ (r i)) ⬝ᵥ residueLatticeCoordinateMap O κ P = 0)
    (hJ : ∀ v : Fin n → κ, (fun i => algebraMap O κ (r i)) ⬝ᵥ v = 0 →
      (fun i => algebraMap O κ (r i)) ⬝ᵥ (J.map (algebraMap O κ) *ᵥ v) = 0)
    (b q : Fin n → κ) (hqP : q ⬝ᵥ residueLatticeCoordinateMap O κ P = 0)
    (hb : ∃ v : Fin n → κ, (fun i => algebraMap O κ (r i)) ⬝ᵥ v = 0 ∧ b ⬝ᵥ v ≠ 0)
    (γ : κ)
    (hproportional : ∀ v : Fin n → κ, (fun i => algebraMap O κ (r i)) ⬝ᵥ v = 0 →
      q ⬝ᵥ v = γ * (b ⬝ᵥ v))
    (htransport : ∀ v : Fin n → κ, (fun i => algebraMap O κ (r i)) ⬝ᵥ v = 0 →
      q ⬝ᵥ (J.map (algebraMap O κ) *ᵥ v) = b ⬝ᵥ v) :
    ¬ IsNilpotent (simplePoleMatrix F π m J P r s) := by
  intro hnil
  let M := residueTangentLattice κ r
  let i : M →ₗ[O] (Fin n → F) := residueTangentLatticeEmbedding F κ r
  have hi : Function.Injective i := residueTangentLatticeEmbedding_injective hinj r
  let A : Module.End F (Fin n → F) := (simplePoleMatrix F π m J P r s).toLin'
  let B : Module.End O (Fin n → F) := A.restrictScalars O
  have hstable (w : M) : B (i w) ∈ LinearMap.range i := by
    obtain ⟨w', _t, himage, _hred⟩ :=
      simplePoleMatrix_constructs_tangent_lattice_image π m J P r s hπF hπκ hP hJ w
    exact ⟨w', himage⟩
  let T : Module.End O M := (LinearEquiv.ofInjective i hi).symm.toLinearMap.comp
    ((B.comp i).codRestrict (LinearMap.range i) hstable)
  have hcompat (w : M) : i (T w) = A (i w) := by
    change i ((LinearEquiv.ofInjective i hi).symm ⟨B (i w), hstable w⟩) = A (i w)
    exact LinearEquiv.ofInjective_symm_apply i (h := hi) _
  have hA : IsNilpotent A := by
    obtain ⟨k, hk⟩ := hnil
    refine ⟨k, ?_⟩
    change (simplePoleMatrix F π m J P r s).toLin' ^ k = 0
    rw [← Matrix.toLin'_pow, hk]
    simp
  let l : M →ₗ[O] κ := residueTangentFunctional r b
  have hl : l ≠ 0 := residueTangentFunctional_ne_zero hsurj r b hb
  apply no_nilpotent_lattice_covector_transport A hA T i hi hcompat l hl γ
  intro w
  obtain ⟨w', t, himage, hred⟩ :=
    simplePoleMatrix_constructs_tangent_lattice_image π m J P r s hπF hπκ hP hJ w
  have hTw : T w = w' := hi ((hcompat w).trans himage.symm)
  rw [hTw]
  change γ * (b ⬝ᵥ residueTangentLatticeReduction κ r w') = b ⬝ᵥ residueTangentLatticeReduction κ r w
  calc
    _ = q ⬝ᵥ residueTangentLatticeReduction κ r w' :=
      (hproportional _ (residueTangentLatticeReduction_tangent r w')).symm
    _ = q ⬝ᵥ (J.map (algebraMap O κ) *ᵥ residueTangentLatticeReduction κ r w) +
        (q ⬝ᵥ residueLatticeCoordinateMap O κ P) * t := by
      rw [hred]
      simp only [dotProduct, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      change q j * (algebraMap O κ (P j) * t) = q j * algebraMap O κ (P j) * t
      ring
    _ = _ := by rw [hqP, zero_mul, add_zero, htransport _ (residueTangentLatticeReduction_tangent r w)]

/-- The exact local data of Lemma 4.3 give the contradiction with
nilpotence, including construction of the proportionality scalar from
the common tangent kernel. No invariant lattice, quotient, eigenvalue,
functional or proportionality scalar is an extra hypothesis. -/
theorem simplePoleMatrix_not_isNilpotent_of_common_tangent_kernel
    (hinj : Function.Injective (algebraMap O F)) (hsurj : Function.Surjective (algebraMap O κ))
    (π m : O) (J : Matrix (Fin n) (Fin n) O) (P r s : Fin n → O)
    (hπF : algebraMap O F π ≠ 0)
    (hπκ : RingHom.ker (algebraMap O κ) = Ideal.span {π})
    (hP : (fun i => algebraMap O κ (r i)) ⬝ᵥ residueLatticeCoordinateMap O κ P = 0)
    (hJ : ∀ v : Fin n → κ, (fun i => algebraMap O κ (r i)) ⬝ᵥ v = 0 →
      (fun i => algebraMap O κ (r i)) ⬝ᵥ (J.map (algebraMap O κ) *ᵥ v) = 0)
    (b q : Fin n → κ) (hbP : b ⬝ᵥ residueLatticeCoordinateMap O κ P = 0)
    (hb : ∃ v : Fin n → κ, (fun i => algebraMap O κ (r i)) ⬝ᵥ v = 0 ∧ b ⬝ᵥ v ≠ 0)
    (hker : ∀ v : Fin n → κ, (fun i => algebraMap O κ (r i)) ⬝ᵥ v = 0 →
      (b ⬝ᵥ v = 0 ↔ q ⬝ᵥ v = 0))
    (htransport : ∀ v : Fin n → κ, (fun i => algebraMap O κ (r i)) ⬝ᵥ v = 0 →
      q ⬝ᵥ (J.map (algebraMap O κ) *ᵥ v) = b ⬝ᵥ v) :
    ¬ IsNilpotent (simplePoleMatrix F π m J P r s) := by
  obtain ⟨γ, _hγ, hproportional⟩ := covectors_same_tangent_kernel_proportional _ b q hb hker
  exact simplePoleMatrix_not_isNilpotent_of_covector_transport hinj hsurj π m J P r s hπF hπκ hP hJ
    b q ((hker _ hP).mp hbP) hb γ hproportional htransport

end DimensionFourDependence
