import DimensionFourDependence.Defs

/-! # A generating root bounds the actual extension degree -/

namespace DimensionFourDependence

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A nonzero polynomial relation for a field generator constructs
finiteness and bounds the actual field degree by the polynomial degree. -/
theorem generating_root_finite_and_degree_le
    (x : L) (hgen : IntermediateField.adjoin K {x} = ⊤)
    (p : Polynomial K) (hp : p ≠ 0) (hroot : Polynomial.aeval x p = 0) :
    Module.Finite K L ∧ Module.finrank K L ≤ p.natDegree := by
  have hx : IsIntegral K x := IsAlgebraic.isIntegral ⟨p, hp, hroot⟩
  have hfinite : Module.Finite K L := by
    let : Module.Finite K (IntermediateField.adjoin K {x}) := IntermediateField.adjoin.finiteDimensional hx
    apply Module.Finite.of_surjective (IntermediateField.adjoin K {x}).val.toLinearMap
    intro y
    have hy : y ∈ IntermediateField.adjoin K {x} := by rw [hgen]; trivial
    exact ⟨⟨y, hy⟩, rfl⟩
  refine ⟨hfinite, ?_⟩
  have hdegree : Module.finrank K L = (minpoly K x).natDegree := by
    rw [← IntermediateField.finrank_top', ← hgen, IntermediateField.adjoin.finrank hx]
  rw [hdegree]
  exact Polynomial.natDegree_le_of_dvd (minpoly.dvd K x hroot) hp

end DimensionFourDependence
