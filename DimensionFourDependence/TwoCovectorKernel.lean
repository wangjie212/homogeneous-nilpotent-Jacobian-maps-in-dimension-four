import DimensionFourDependence.RankTwoIsotropicPlane
import DimensionFourDependence.AffineLineDerivation

/-! # A radial common kernel and affine-line containment

Two independent covectors in three variables have a one-dimensional
common kernel. A nonzero radial vector in that kernel therefore fixes
the tangent direction. Exact derivation constants integrate that direction.
-/

namespace DimensionFourDependence

open Matrix Module

variable {F : Type*} [Field F]

/-- A nonzero vector in the common kernel of two independent covectors
spans that common kernel. -/
theorem two_covector_common_kernel
    (a b Y u : Fin 3 → F) (hab : LinearIndependent F ![a, b]) (hY : Y ≠ 0)
    (haY : a ⬝ᵥ Y = 0) (hbY : b ⬝ᵥ Y = 0)
    (hau : a ⬝ᵥ u = 0) (hbu : b ⬝ᵥ u = 0) : ∃ r : F, r • Y = u := by
  let N : Matrix (Fin 2) (Fin 3) F := ![a, b]
  have hr : N.rank = 2 := hab.rank_matrix
  have hd := LinearMap.finrank_range_add_finrank_ker N.toLin'
  have hr' : finrank F (LinearMap.range N.toLin') = 2 := hr
  simp only [Module.finrank_pi, Fintype.card_fin] at hd
  have hk : finrank F (LinearMap.ker N.toLin') = 1 := by omega
  have hNY : N *ᵥ Y = 0 := by
    funext i
    fin_cases i <;> assumption
  have hNu : N *ᵥ u = 0 := by
    funext i
    fin_cases i <;> assumption
  let y : LinearMap.ker N.toLin' := ⟨Y, hNY⟩
  have hy : y ≠ 0 := fun he => hY (congrArg Subtype.val he)
  obtain ⟨r, he⟩ := (finrank_eq_one_iff_of_nonzero' y hy).mp hk ⟨u, hNu⟩
  exact ⟨r, congrArg Subtype.val he⟩

variable {E : Type*} [Field E] [Algebra E F] {n : ℕ}

/-- A tangent which is a variable multiple of a scalar direction puts
the entire curve on an affine line, when all derivation constants are scalars. -/
theorem liesInAffineLine_of_scalar_tangent_direction
    (D : Derivation E F F) (x : Fin n → F)
    (hconst : ∀ z : F, D z = 0 → ∃ c : E, algebraMap E F c = z)
    (v : Fin n → E) (r : F) (hu : (fun i => D (x i)) ≠ 0)
    (hdir : ∀ i, D (x i) = r * algebraMap E F (v i)) :
    LiesInAffineLine (E := E) x := by
  obtain ⟨j, hj⟩ : ∃ j, D (x j) ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hu
  have hvj : v j ≠ 0 := by
    intro he
    exact hj (by rw [hdir j, he, map_zero, mul_zero])
  apply liesInAffineLine_of_derivative_ratios D x hconst j hj
  intro i
  refine ⟨v i / v j, ?_⟩
  rw [map_div₀, hdir i, hdir j]
  have hm : algebraMap E F (v j) ≠ 0 := by
    simpa only [map_zero] using (algebraMap E F).injective.ne hvj
  field_simp

end DimensionFourDependence
