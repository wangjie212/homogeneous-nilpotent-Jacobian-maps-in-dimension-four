import DimensionFourDependence.TernaryTangentDecomposition
import DimensionFourDependence.ParameterDirectionAlgebraicity

/-! # Three actual normal jets construct the nonlinear directrix tangent and decomposition -/

namespace DimensionFourDependence

open Matrix Module

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- A nonzero direction annihilated by the first two independent
normal jets cannot be annihilated by the third. -/
theorem independent_ternary_normal_jet_last_pairing_ne_zero
    (ν ν₁ ν₂ V : Fin 3 → F) (hjet : LinearIndependent F ![ν, ν₁, ν₂])
    (hV : V ≠ 0) (hνV : ν ⬝ᵥ V = 0) (hν₁V : ν₁ ⬝ᵥ V = 0) : ν₂ ⬝ᵥ V ≠ 0 := by
  intro hz
  let N : Matrix (Fin 3) (Fin 3) F := ![ν, ν₁, ν₂]
  have hr : N.rank = 3 := hjet.rank_matrix
  have hd := LinearMap.finrank_range_add_finrank_ker N.toLin'
  have hrange : finrank F (LinearMap.range N.toLin') = 3 := hr
  simp only [Module.finrank_pi, Fintype.card_fin] at hd
  have hdim : finrank F (LinearMap.ker N.toLin') = 0 := by omega
  have hker : LinearMap.ker N.toLin' = ⊥ := Submodule.finrank_eq_zero.mp hdim
  have hNV : N *ᵥ V = 0 := by funext i; fin_cases i <;> assumption
  have hm : V ∈ LinearMap.ker N.toLin' := hNV
  rw [hker, Submodule.mem_bot] at hm
  exact hV hm

/-- The first two actual normal incidences and the independent third
jet construct independent directrix and directrix-derivative directions. -/
theorem independent_normal_jets_construct_directrix_tangent_pair
    (T : Derivation K F F) (ν V : Fin 3 → F)
    (hjet : LinearIndependent F ![ν, (fun i => T (ν i)), (fun i => T (T (ν i)))])
    (hV : V ≠ 0) (hνV : ν ⬝ᵥ V = 0) (hν₁V : (fun i => T (ν i)) ⬝ᵥ V = 0) :
    ν ⬝ᵥ (fun i => T (V i)) = 0 ∧ LinearIndependent F ![V, (fun i => T (V i))] := by
  have hthird := independent_ternary_normal_jet_last_pairing_ne_zero
    ν (fun i => T (ν i)) (fun i => T (T (ν i))) V hjet hV hνV hν₁V
  have hνTV : ν ⬝ᵥ (fun i => T (V i)) = 0 := by
    have he := congrArg T hνV
    rw [derivation_dotProduct, hν₁V, zero_add, map_zero] at he
    exact he
  refine ⟨hνTV, (LinearIndependent.pair_iff' hV).mpr ?_⟩
  intro r hr
  have he := congrArg T hν₁V
  rw [derivation_dotProduct, map_zero] at he
  have hz : (fun i => T (ν i)) ⬝ᵥ (fun i => T (V i)) = 0 := by
    rw [← hr, dotProduct_smul, hν₁V, smul_zero]
  rw [hz, add_zero] at he
  exact hthird he

variable [CharZero K] [CharZero F]

/-- The actual independent normal jets and parameter-algebraic
projected fiber direction construct alpha,beta with beta != 0, both
parameter-algebraic, and V_t = alpha V + beta A. No decomposition or
nonlinear directrix-tangent hypothesis is supplied. -/
theorem parameter_normal_jets_construct_algebraic_directrix_decomposition
    (p : RatFunc K →ₐ[K] F) (T : Derivation K F F) (hT : T (p RatFunc.X) = 1)
    (ν V A : Fin 3 → F)
    (hjet : LinearIndependent F ![ν, (fun i => T (ν i)), (fun i => T (T (ν i)))])
    (hVA : LinearIndependent F ![V, A])
    (hνV : ν ⬝ᵥ V = 0) (hν₁V : (fun i => T (ν i)) ⬝ᵥ V = 0) (hνA : ν ⬝ᵥ A = 0)
    (hV : ∀ i, IsAlgebraic p.fieldRange (V i)) (hA : ∀ i, IsAlgebraic p.fieldRange (A i)) :
    ∃ α β : F, β ≠ 0 ∧ IsAlgebraic p.fieldRange α ∧ IsAlgebraic p.fieldRange β ∧
      ∀ i : Fin 3, T (V i) = α * V i + β * A i := by
  have hV0 : V ≠ 0 := by simpa using hVA.ne_zero (0 : Fin 2)
  have hν0 : ν ≠ 0 := by simpa using hjet.ne_zero (0 : Fin 3)
  obtain ⟨hνTV, hVT⟩ := independent_normal_jets_construct_directrix_tangent_pair T ν V hjet hV0 hνV hν₁V
  exact algebraic_ternary_tangent_plane_constructs_decomposition ν V A (fun i => T (V i)) hν0 hVA hVT
    hνV hνA hνTV hV hA (fun i => rational_parameter_derivative_preserves_algebraic_coefficients p T hT _ (hV i))

end DimensionFourDependence
