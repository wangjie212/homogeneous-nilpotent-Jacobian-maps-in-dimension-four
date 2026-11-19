import DimensionFourDependence.RulingFormCoordinateSpan

/-! # The original coordinate-span coefficient vectors are independent

If every vector of a two-dimensional ruling is a combination of two
coefficient vectors, their span contains that ruling and has dimension
at least two. The coefficient pair is therefore independent.
-/

namespace DimensionFourDependence

open Matrix Module

variable {F : Type*} [Field F] {n : ℕ}

/-- Original coordinate-span expressions put the actual ruling
inside the span of their two coefficient vectors. -/
theorem ruling_coordinate_span_contains_ruling
    (W : Submodule F (Fin n → F)) (s t bS bN : Fin n → F)
    (hspan : ∀ x ∈ W, ∀ i, x i = bS i * (s ⬝ᵥ x) + bN i * (t ⬝ᵥ x)) :
    W ≤ Submodule.span F (Set.range ![bS, bN]) := by
  let U := Submodule.span F (Set.range ![bS, bN])
  have hbS : bS ∈ U := Submodule.subset_span ⟨0, rfl⟩
  have hbN : bN ∈ U := Submodule.subset_span ⟨1, rfl⟩
  intro x hx
  have hxrep : x = (s ⬝ᵥ x) • bS + (t ⬝ᵥ x) • bN := by
    funext i
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hspan x hx i
  rw [hxrep]
  exact U.add_mem (U.smul_mem _ hbS) (U.smul_mem _ hbN)

/-- Coordinate expressions for a two-dimensional ruling automatically
give independent original coefficient vectors. -/
theorem ruling_coordinate_span_vectors_independent
    (W : Submodule F (Fin n → F)) (hdim : finrank F W = 2)
    (s t bS bN : Fin n → F)
    (hspan : ∀ x ∈ W, ∀ i, x i = bS i * (s ⬝ᵥ x) + bN i * (t ⬝ᵥ x)) :
    LinearIndependent F ![bS, bN] := by
  let U := Submodule.span F (Set.range ![bS, bN])
  have hWU : W ≤ U := ruling_coordinate_span_contains_ruling W s t bS bN hspan
  apply linearIndependent_iff_card_le_finrank_span.mpr
  change 2 ≤ finrank F U
  rw [← hdim]
  exact Submodule.finrank_mono hWU

/-- Those two original coefficient vectors belong to the actual
two-dimensional ruling itself. -/
theorem ruling_coordinate_span_vectors_mem
    (W : Submodule F (Fin n → F)) (hdim : finrank F W = 2)
    (s t bS bN : Fin n → F)
    (hspan : ∀ x ∈ W, ∀ i, x i = bS i * (s ⬝ᵥ x) + bN i * (t ⬝ᵥ x)) :
    bS ∈ W ∧ bN ∈ W := by
  let U := Submodule.span F (Set.range ![bS, bN])
  have hWU : W ≤ U := ruling_coordinate_span_contains_ruling W s t bS bN hspan
  have hUdim : finrank F U = 2 := by
    simpa only [Fintype.card_fin] using
      finrank_span_eq_card (ruling_coordinate_span_vectors_independent W hdim s t bS bN hspan)
  have hWUeq : W = U := Submodule.eq_of_le_of_finrank_eq hWU (hdim.trans hUdim.symm)
  rw [hWUeq]
  exact ⟨Submodule.subset_span ⟨0, rfl⟩, Submodule.subset_span ⟨1, rfl⟩⟩

/-- The original coefficient vectors are exactly dual to the two
actual ruling forms, including both zero cross-pairings. -/
theorem ruling_coordinate_span_dual_values
    (W : Submodule F (Fin n → F)) (hdim : finrank F W = 2)
    (s t bS bN : Fin n → F)
    (hspan : ∀ x ∈ W, ∀ i, x i = bS i * (s ⬝ᵥ x) + bN i * (t ⬝ᵥ x)) :
    s ⬝ᵥ bS = 1 ∧ t ⬝ᵥ bS = 0 ∧ s ⬝ᵥ bN = 0 ∧ t ⬝ᵥ bN = 1 := by
  have hpair := ruling_coordinate_span_vectors_independent W hdim s t bS bN hspan
  have hmem := ruling_coordinate_span_vectors_mem W hdim s t bS bN hspan
  rw [LinearIndependent.pair_iff] at hpair
  have heS : (s ⬝ᵥ bS - 1) • bS + (t ⬝ᵥ bS) • bN = 0 := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hi := hspan bS hmem.1 i
    linear_combination -hi
  have heN : (s ⬝ᵥ bN) • bS + (t ⬝ᵥ bN - 1) • bN = 0 := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hi := hspan bN hmem.2 i
    linear_combination -hi
  have hvS := hpair _ _ heS
  have hvN := hpair _ _ heN
  exact ⟨sub_eq_zero.mp hvS.1, hvS.2, hvN.1, sub_eq_zero.mp hvN.2⟩

/-- Two independent ruling forms construct both independent original
coefficient vectors and every original coordinate expression. -/
theorem two_dimensional_ruling_independent_coordinate_span
    (W : Submodule F (Fin n → F)) (hdim : finrank F W = 2) (s t : Fin n → F)
    (hpair : LinearIndependent F ![rulingFormRestriction W s, rulingFormRestriction W t]) :
    ∃ bS bN : Fin n → F, LinearIndependent F ![bS, bN] ∧
      ∀ x ∈ W, ∀ i, x i = bS i * (s ⬝ᵥ x) + bN i * (t ⬝ᵥ x) := by
  obtain ⟨bS, bN, hspan⟩ := two_dimensional_ruling_coordinate_form_span W hdim s t hpair
  exact ⟨bS, bN, ruling_coordinate_span_vectors_independent W hdim s t bS bN hspan, hspan⟩

/-- Two independent ruling forms construct their actual original
coordinate basis, all four dual pairings, and all coordinate expressions. -/
theorem two_dimensional_ruling_coordinate_basis
    (W : Submodule F (Fin n → F)) (hdim : finrank F W = 2) (s t : Fin n → F)
    (hpair : LinearIndependent F ![rulingFormRestriction W s, rulingFormRestriction W t]) :
    ∃ bS bN : Fin n → F, LinearIndependent F ![bS, bN] ∧ bS ∈ W ∧ bN ∈ W ∧
      s ⬝ᵥ bS = 1 ∧ t ⬝ᵥ bS = 0 ∧ s ⬝ᵥ bN = 0 ∧ t ⬝ᵥ bN = 1 ∧
      ∀ x ∈ W, ∀ i, x i = bS i * (s ⬝ᵥ x) + bN i * (t ⬝ᵥ x) := by
  obtain ⟨bS, bN, hspan⟩ := two_dimensional_ruling_coordinate_form_span W hdim s t hpair
  have hmem := ruling_coordinate_span_vectors_mem W hdim s t bS bN hspan
  have hvalues := ruling_coordinate_span_dual_values W hdim s t bS bN hspan
  exact ⟨bS, bN, ruling_coordinate_span_vectors_independent W hdim s t bS bN hspan,
    hmem.1, hmem.2, hvalues.1, hvalues.2.1, hvalues.2.2.1, hvalues.2.2.2, hspan⟩

end DimensionFourDependence
