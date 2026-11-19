import DimensionFourDependence.ResidueTangentLattice

/-! # The simple-pole Jacobian preserves the actual tangent lattice

The pole is a rank-one correction in the tangent direction P. Divisibility
of the integral normal pairing cancels its denominator on the lattice.
-/

namespace DimensionFourDependence

open Matrix

variable {O : Type*} [CommRing O] {n : ℕ}

/-- The normalized Jacobian with its single normal pole and regular remainder. -/
def simplePoleMatrix (F : Type*) [Field F] [Algebra O F]
    (π m : O) (J : Matrix (Fin n) (Fin n) O) (P r s : Fin n → O) :
    Matrix (Fin n) (Fin n) F := fun i j => algebraMap O F (J i j) +
      algebraMap O F (P i) * (algebraMap O F m * algebraMap O F (r j) / algebraMap O F π +
        algebraMap O F (s j))

variable {F : Type*} [Field F] [Algebra O F]

/-- The exact original-coordinate action before cancellation of the pole. -/
theorem simplePoleMatrix_action
    (π m : O) (J : Matrix (Fin n) (Fin n) O) (P r s w : Fin n → O) (i : Fin n) :
    (simplePoleMatrix F π m J P r s *ᵥ residueLatticeCoordinateMap O F w) i =
      algebraMap O F ((J *ᵥ w) i) + algebraMap O F (P i) *
        (algebraMap O F m * algebraMap O F (r ⬝ᵥ w) / algebraMap O F π + algebraMap O F (s ⬝ᵥ w)) := by
  calc
    _ = (∑ j, algebraMap O F (J i j) * algebraMap O F (w j)) + algebraMap O F (P i) *
        ∑ j, (algebraMap O F m * algebraMap O F (r j) / algebraMap O F π +
          algebraMap O F (s j)) * algebraMap O F (w j) := by
      change (∑ j, (algebraMap O F (J i j) + algebraMap O F (P i) *
        (algebraMap O F m * algebraMap O F (r j) / algebraMap O F π + algebraMap O F (s j))) *
          algebraMap O F (w j)) = _
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      congr 1
      · simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      · congr 1
        simp only [dotProduct, map_sum, map_mul, div_eq_mul_inv, add_mul,
          Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- Divisibility of the integral normal pairing cancels the actual pole. -/
theorem simplePoleMatrix_integral_action
    (π m : O) (J : Matrix (Fin n) (Fin n) O) (P r s w : Fin n → O)
    (hπ : algebraMap O F π ≠ 0) (a : O) (ha : r ⬝ᵥ w = π * a) :
    simplePoleMatrix F π m J P r s *ᵥ residueLatticeCoordinateMap O F w =
      residueLatticeCoordinateMap O F (fun i => (J *ᵥ w) i + P i * (m * a + s ⬝ᵥ w)) := by
  ext i
  rw [simplePoleMatrix_action, ha, map_mul]
  change _ = algebraMap O F ((J *ᵥ w) i + P i * (m * a + s ⬝ᵥ w))
  simp only [map_add, map_mul]
  field_simp

variable {κ : Type*} [CommRing κ] [Algebra O κ]

/-- Every integral rank-one update has its exact original residue
pairing, including its scalar correction in the direction P. -/
theorem residue_pairing_integral_rank_one_update
    (b : Fin n → κ) (J : Matrix (Fin n) (Fin n) O) (P w : Fin n → O) (t : O) :
    b ⬝ᵥ residueLatticeCoordinateMap O κ (fun i => (J *ᵥ w) i + P i * t) =
      b ⬝ᵥ (J.map (algebraMap O κ) *ᵥ residueLatticeCoordinateMap O κ w) +
        (b ⬝ᵥ residueLatticeCoordinateMap O κ P) * algebraMap O κ t := by
  change (∑ i, b i * algebraMap O κ ((J *ᵥ w) i + P i * t)) = _
  simp only [dotProduct, map_add, map_mul, map_sum, Matrix.mulVec, Matrix.map_apply,
    residueLatticeCoordinateMap, LinearMap.coe_mk, AddHom.coe_mk, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul]
  congr 1; apply Finset.sum_congr rfl; intros; ring

/-- The explicit simple-pole matrix constructs an integral tangent
image with its exact reduced rank-one correction. No lattice stability
or integral action is an extra hypothesis. -/
theorem simplePoleMatrix_constructs_tangent_lattice_image
    (π m : O) (J : Matrix (Fin n) (Fin n) O) (P r s : Fin n → O)
    (hπF : algebraMap O F π ≠ 0)
    (hπκ : RingHom.ker (algebraMap O κ) = Ideal.span {π})
    (hP : (fun i => algebraMap O κ (r i)) ⬝ᵥ residueLatticeCoordinateMap O κ P = 0)
    (hJ : ∀ v : Fin n → κ, (fun i => algebraMap O κ (r i)) ⬝ᵥ v = 0 →
      (fun i => algebraMap O κ (r i)) ⬝ᵥ (J.map (algebraMap O κ) *ᵥ v) = 0)
    (w : residueTangentLattice κ r) :
    ∃ (w' : residueTangentLattice κ r) (t : κ),
      residueTangentLatticeEmbedding F κ r w' =
        simplePoleMatrix F π m J P r s *ᵥ residueTangentLatticeEmbedding F κ r w ∧
      residueTangentLatticeReduction κ r w' = fun i =>
        (J.map (algebraMap O κ) *ᵥ residueTangentLatticeReduction κ r w) i + algebraMap O κ (P i) * t := by
  obtain ⟨a, ha⟩ := residueTangentLattice_normal_pairing_dvd π hπκ r w
  let t : O := m * a + s ⬝ᵥ (w : Fin n → O)
  let z : Fin n → O := fun i => (J *ᵥ (w : Fin n → O)) i + P i * t
  have hmem : z ∈ residueTangentLattice κ r := by
    change algebraMap O κ (r ⬝ᵥ z) = 0
    have he : algebraMap O κ (r ⬝ᵥ z) =
        (fun i => algebraMap O κ (r i)) ⬝ᵥ residueLatticeCoordinateMap O κ z := by
      simp only [dotProduct, map_sum, map_mul]
      rfl
    rw [he, residue_pairing_integral_rank_one_update]
    have hJw := hJ (residueLatticeCoordinateMap O κ (w : Fin n → O))
      (residueTangentLatticeReduction_tangent r w)
    rw [hJw, hP, zero_mul, zero_add]
  refine ⟨⟨z, hmem⟩, algebraMap O κ t, ?_, ?_⟩
  · exact (simplePoleMatrix_integral_action π m J P r s (w : Fin n → O) hπF a ha).symm
  · ext i
    change algebraMap O κ ((J *ᵥ (w : Fin n → O)) i + P i * t) = _
    simp only [map_add, map_mul, Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
    rfl

end DimensionFourDependence
