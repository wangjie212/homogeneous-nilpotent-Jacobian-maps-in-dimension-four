import DimensionFourDependence.NilpotentFunctionalTransport

/-! # The actual tangent residue lattice used in Lemma 4.3 -/

namespace DimensionFourDependence

open Matrix

/-- Coordinatewise algebra inclusion, as a linear map over the original ring. -/
def residueLatticeCoordinateMap (O A : Type*) [CommRing O] [CommRing A] [Algebra O A] {n : ℕ} :
    (Fin n → O) →ₗ[O] (Fin n → A) where
  toFun w i := algebraMap O A (w i)
  map_add' := by intro w v; ext i; exact map_add (algebraMap O A) _ _
  map_smul' := by
    intro a w
    ext i
    exact (Algebra.linearMap O A).map_smul a (w i)

variable {O : Type*} [CommRing O] {n : ℕ}

/-- Integral vectors whose normal pairing vanishes in the residue field. -/
def residueTangentLattice (κ : Type*) [CommRing κ] [Algebra O κ] (r : Fin n → O) :
    Submodule O (Fin n → O) :=
  LinearMap.ker ((Algebra.linearMap O κ).comp ((dotProductBilin O O) r))

/-- The original-coordinate realization of the tangent lattice in
the fraction vector space. -/
def residueTangentLatticeEmbedding (F κ : Type*) [CommRing F] [CommRing κ]
    [Algebra O F] [Algebra O κ] (r : Fin n → O) :
    residueTangentLattice κ r →ₗ[O] (Fin n → F) :=
  (residueLatticeCoordinateMap O F).comp (residueTangentLattice κ r).subtype

/-- The original-coordinate reduction of the tangent lattice. -/
def residueTangentLatticeReduction (κ : Type*) [CommRing κ] [Algebra O κ] (r : Fin n → O) :
    residueTangentLattice κ r →ₗ[O] (Fin n → κ) :=
  (residueLatticeCoordinateMap O κ).comp (residueTangentLattice κ r).subtype

variable {F κ : Type*} [CommRing F] [CommRing κ] [Algebra O F] [Algebra O κ]

/-- Faithfulness of the original ring inclusion makes the lattice
realization faithful, without a freeness or finite-generation assumption. -/
theorem residueTangentLatticeEmbedding_injective
    (hinj : Function.Injective (algebraMap O F)) (r : Fin n → O) :
    Function.Injective (residueTangentLatticeEmbedding F κ r) := by
  intro w v he
  apply Subtype.ext
  funext i
  exact hinj (congrFun he i)

omit [CommRing F] [Algebra O F] in
/-- Every reduced lattice vector lies in the actual residue tangent hyperplane. -/
theorem residueTangentLatticeReduction_tangent (r : Fin n → O) (w : residueTangentLattice κ r) :
    (fun i => algebraMap O κ (r i)) ⬝ᵥ residueTangentLatticeReduction κ r w = 0 := by
  have he : algebraMap O κ (r ⬝ᵥ (w : Fin n → O)) = 0 := w.property
  simpa [dotProduct, residueTangentLatticeReduction, residueLatticeCoordinateMap,
    map_sum, map_mul] using he

omit [CommRing F] [Algebra O F] in
/-- Surjective residue reduction lifts every actual residue tangent
vector to the original integral tangent lattice. -/
theorem residueTangentLatticeReduction_surjective_on_tangent
    (hsurj : Function.Surjective (algebraMap O κ)) (r : Fin n → O) (v : Fin n → κ)
    (hv : (fun i => algebraMap O κ (r i)) ⬝ᵥ v = 0) :
    ∃ w : residueTangentLattice κ r, residueTangentLatticeReduction κ r w = v := by
  choose w hw using fun i => hsurj (v i)
  have hmem : w ∈ residueTangentLattice κ r := by
    change algebraMap O κ (r ⬝ᵥ w) = 0
    simpa only [dotProduct, map_sum, map_mul, hw] using hv
  exact ⟨⟨w, hmem⟩, funext hw⟩

omit [CommRing F] [Algebra O F] in
/-- A principal residue kernel makes the integral normal pairing of
every lattice vector divisible by the same original uniformizer. -/
theorem residueTangentLattice_normal_pairing_dvd
    (π : O) (hπ : RingHom.ker (algebraMap O κ) = Ideal.span {π})
    (r : Fin n → O) (w : residueTangentLattice κ r) : π ∣ r ⬝ᵥ (w : Fin n → O) := by
  have he : r ⬝ᵥ (w : Fin n → O) ∈ RingHom.ker (algebraMap O κ) := w.property
  rwa [hπ, Ideal.mem_span_singleton] at he

omit [CommRing F] [Algebra O F] in
/-- An actual residue covector evaluated on the actual tangent lattice. -/
def residueTangentFunctional (r : Fin n → O) (b : Fin n → κ) :
    residueTangentLattice κ r →ₗ[O] κ :=
  (((dotProductBilin κ κ) b).restrictScalars O).comp (residueTangentLatticeReduction κ r)

omit [CommRing F] [Algebra O F] in
/-- A nonzero covector on the residue tangent hyperplane supplies a
nonzero actual lattice functional, using the constructed residue lift. -/
theorem residueTangentFunctional_ne_zero
    (hsurj : Function.Surjective (algebraMap O κ)) (r : Fin n → O) (b : Fin n → κ)
    (hb : ∃ v : Fin n → κ, (fun i => algebraMap O κ (r i)) ⬝ᵥ v = 0 ∧ b ⬝ᵥ v ≠ 0) :
    residueTangentFunctional r b ≠ 0 := by
  obtain ⟨v, hv, hbv⟩ := hb
  obtain ⟨w, hw⟩ := residueTangentLatticeReduction_surjective_on_tangent hsurj r v hv
  intro hz
  have he := congrArg (fun l : residueTangentLattice κ r →ₗ[O] κ => l w) hz
  change b ⬝ᵥ residueTangentLatticeReduction κ r w = 0 at he
  rw [hw] at he
  exact hbv he

end DimensionFourDependence
