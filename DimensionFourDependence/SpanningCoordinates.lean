import DimensionFourDependence.ImageNormalDerivation

/-! # Independent coordinate rows of a spanning family -/

namespace DimensionFourDependence

open Module

variable {K V ι ρ : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ρ]

/-- The coordinate rows of a spanning family are linearly independent.
This constructs independent constant covectors from a basis of the
constant span of the components of a polynomial normal. -/
theorem basis_coordinate_rows_independent (b : Basis ρ K V) (x : ι → V)
    (hx : Submodule.span K (Set.range x) = ⊤) :
    LinearIndependent K (fun j : ρ => fun i : ι => b.repr (x i) j) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  let L : V →ₗ[K] K := ∑ k, c k • b.coord k
  have hzero (i : ι) : L (x i) = 0 := by
    have he := congrFun hc i
    simpa [L, Basis.coord_apply] using he
  have hker : Submodule.span K (Set.range x) ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hzero i
  have hL : L = 0 := LinearMap.ker_eq_top.mp (top_le_iff.mp (hx ▸ hker))
  have hj := DFunLike.congr_fun hL (b j)
  simpa [L, Basis.coord_apply, Finsupp.single_apply] using hj

/-- The original generators span their own span when regarded as elements of it. -/
theorem generators_span_subtype_top (x : ι → V) :
    Submodule.span K (Set.range (fun i =>
      (⟨x i, Submodule.subset_span (Set.mem_range_self i)⟩ : Submodule.span K (Set.range x)))) = ⊤ :=
  (Submodule.span_range_subtype_eq_top_iff _ _).mpr rfl

end DimensionFourDependence
