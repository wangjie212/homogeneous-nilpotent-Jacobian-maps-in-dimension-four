import DimensionFourDependence.LineChartPivots
import DimensionFourDependence.ConeQuadraticCoefficient

/-! # The actual ternary tangent plane constructs the directrix derivative decomposition -/

namespace DimensionFourDependence

open Matrix Module

set_option maxHeartbeats 3000000

variable {F : Type*} [Field F]

/-- Two independent directions annihilated by a nonzero ternary
normal span its entire tangent plane. -/
theorem ternary_covector_kernel_eq_independent_pair_span
    (ν V A : Fin 3 → F) (hν : ν ≠ 0) (hVA : LinearIndependent F ![V, A])
    (hνV : ν ⬝ᵥ V = 0) (hνA : ν ⬝ᵥ A = 0) :
    LinearMap.ker ((dotProductBilin F F) ν) = Submodule.span F (Set.range ![V, A]) := by
  classical
  let l := (dotProductBilin F F) ν
  obtain ⟨j, hj⟩ : ∃ j, ν j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hν
  have hsurj : Function.Surjective l := by
    intro c
    refine ⟨Pi.single j (c / ν j), ?_⟩
    change ν ⬝ᵥ Pi.single j (c / ν j) = c
    rw [dotProduct_single]
    field_simp
  have hd := LinearMap.finrank_range_add_finrank_ker l
  rw [LinearMap.range_eq_top.mpr hsurj] at hd
  simp only [finrank_top, finrank_self, Module.finrank_pi, Fintype.card_fin] at hd
  have hker : finrank F (LinearMap.ker l) = 2 := by omega
  have hle : Submodule.span F (Set.range ![V, A]) ≤ LinearMap.ker l := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> assumption
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  simpa only [hker, Fintype.card_fin] using finrank_span_eq_card hVA

/-- The directrix tangent has a unique two-direction expression;
independence from the directrix makes its transverse coefficient nonzero. -/
theorem ternary_tangent_plane_constructs_nonzero_transverse_decomposition
    (ν V A W : Fin 3 → F) (hν : ν ≠ 0)
    (hVA : LinearIndependent F ![V, A]) (hVW : LinearIndependent F ![V, W])
    (hνV : ν ⬝ᵥ V = 0) (hνA : ν ⬝ᵥ A = 0) (hνW : ν ⬝ᵥ W = 0) :
    ∃ α β : F, β ≠ 0 ∧ ∀ i : Fin 3, W i = α * V i + β * A i := by
  have hm : W ∈ Submodule.span F (Set.range ![V, A]) := by
    rw [← ternary_covector_kernel_eq_independent_pair_span ν V A hν hVA hνV hνA]
    exact hνW
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := F)).mp hm
  have hrep (i : Fin 3) : W i = c 0 * V i + c 1 * A i := by
    simpa [Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] using (congrFun hc i).symm
  refine ⟨c 0, c 1, ?_, hrep⟩
  intro hβ
  have hV0 : V ≠ 0 := by simpa using hVA.ne_zero (0 : Fin 2)
  apply (LinearIndependent.pair_iff' hV0).mp hVW (c 0)
  funext i
  simpa only [Pi.smul_apply, smul_eq_mul, hβ, zero_mul, add_zero] using (hrep i).symm

variable {J : Type*} [Field J] [Algebra J F]

/-- The exact two tangent-plane coefficients are algebraic over
the actual parameter field whenever the three direction vectors are.
The proof retains explicit nonzero coordinate minors. -/
theorem independent_pair_decomposition_coefficients_isAlgebraic
    (V A W : Fin 3 → F) (hVA : LinearIndependent F ![V, A])
    (hV : ∀ i, IsAlgebraic J (V i)) (hA : ∀ i, IsAlgebraic J (A i))
    (hW : ∀ i, IsAlgebraic J (W i)) (α β : F)
    (hrep : ∀ i : Fin 3, W i = α * V i + β * A i) :
    IsAlgebraic J α ∧ IsAlgebraic J β := by
  obtain ⟨i, j, hdet⟩ := independent_pair_exists_nonzero_coordinate_minor V A hVA
  have hα : α = (W i * A j - W j * A i) / (V i * A j - V j * A i) := by
    apply (eq_div_iff hdet).mpr
    linear_combination -A j * hrep i + A i * hrep j
  have hβ : β = (V i * W j - V j * W i) / (V i * A j - V j * A i) := by
    apply (eq_div_iff hdet).mpr
    linear_combination V j * hrep i - V i * hrep j
  have hmul (x y : F) (hx : IsAlgebraic J x) (hy : IsAlgebraic J y) :
      x * y ∈ algebraicClosure J F :=
    (algebraicClosure J F).mul_mem (mem_algebraicClosure_iff.mpr hx) (mem_algebraicClosure_iff.mpr hy)
  have hden := (algebraicClosure J F).sub_mem (hmul _ _ (hV i) (hA j)) (hmul _ _ (hV j) (hA i))
  constructor
  · rw [hα]
    exact mem_algebraicClosure_iff.mp ((algebraicClosure J F).div_mem
      ((algebraicClosure J F).sub_mem (hmul _ _ (hW i) (hA j)) (hmul _ _ (hW j) (hA i))) hden)
  · rw [hβ]
    exact mem_algebraicClosure_iff.mp ((algebraicClosure J F).div_mem
      ((algebraicClosure J F).sub_mem (hmul _ _ (hV i) (hW j)) (hmul _ _ (hV j) (hW i))) hden)

/-- The actual tangent plane constructs nonzero transverse and
parameter-algebraic decomposition coefficients simultaneously. -/
theorem algebraic_ternary_tangent_plane_constructs_decomposition
    (ν V A W : Fin 3 → F) (hν : ν ≠ 0)
    (hVA : LinearIndependent F ![V, A]) (hVW : LinearIndependent F ![V, W])
    (hνV : ν ⬝ᵥ V = 0) (hνA : ν ⬝ᵥ A = 0) (hνW : ν ⬝ᵥ W = 0)
    (hV : ∀ i, IsAlgebraic J (V i)) (hA : ∀ i, IsAlgebraic J (A i))
    (hW : ∀ i, IsAlgebraic J (W i)) :
    ∃ α β : F, β ≠ 0 ∧ IsAlgebraic J α ∧ IsAlgebraic J β ∧
      ∀ i : Fin 3, W i = α * V i + β * A i := by
  obtain ⟨α, β, hβ, hrep⟩ := ternary_tangent_plane_constructs_nonzero_transverse_decomposition
    ν V A W hν hVA hVW hνV hνA hνW
  obtain ⟨hαalg, hβalg⟩ := independent_pair_decomposition_coefficients_isAlgebraic V A W hVA hV hA hW α β hrep
  exact ⟨α, β, hβ, hαalg, hβalg, hrep⟩

end DimensionFourDependence
