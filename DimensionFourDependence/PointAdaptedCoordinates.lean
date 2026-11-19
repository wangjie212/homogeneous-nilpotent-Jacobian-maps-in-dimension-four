import DimensionFourDependence.Basic

/-! # Coordinates with a prescribed nonzero point first

An isomorphism of singleton spans extends to an ambient linear
automorphism. In dimension three this gives coordinates sending a
specified nonzero point to the first coordinate vector.
-/

namespace DimensionFourDependence

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A]

/-- A linear automorphism can send any nonzero vector to any other nonzero vector. -/
theorem exists_linearEquiv_map_nonzero_vector (u v : A) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g : A ≃ₗ[F] A, g u = v := by
  let eu := LinearEquiv.toSpanNonzeroSingleton F A u hu
  let ev := LinearEquiv.toSpanNonzeroSingleton F A v hv
  let f := eu.symm.trans ev
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have hf : f (eu 1) = ev 1 := by simp [f]
  have he := hg (eu 1)
  change (f (eu 1) : A) = g (eu 1 : A) at he
  rw [hf] at he
  refine ⟨g, ?_⟩
  simpa [eu, ev] using he.symm

variable [FiniteDimensional F A]

/-- A three-dimensional space admits coordinates with a given projective point first. -/
theorem three_space_coordinates_with_point (hA : Module.finrank F A = 3) (O : A) (hO : O ≠ 0) :
    ∃ e : A ≃ₗ[F] (Fin 3 → F), e O = ![1, 0, 0] := by
  let b := (Module.finBasisOfFinrankEq F A hA).equivFun
  have hb : b O ≠ 0 := by simpa only [map_zero] using b.injective.ne hO
  have he0 : (![1, 0, 0] : Fin 3 → F) ≠ 0 := by
    intro hz
    have h0 := congrFun hz 0
    simp at h0
  obtain ⟨g, hg⟩ := exists_linearEquiv_map_nonzero_vector (F := F) (b O) (![1, 0, 0] : Fin 3 → F) hb he0
  exact ⟨b.trans g, hg⟩

end DimensionFourDependence
