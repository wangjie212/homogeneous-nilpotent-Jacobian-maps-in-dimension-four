import DimensionFourDependence.ConstantVertexGaussDimension
import DimensionFourDependence.ThirdInvariant

/-! # The actual homogeneous Gauss image has dimension at most two

The original output radial vector is nonzero and lies in the actual
coefficient Hessian kernel. Rank-nullity and the checked identification
with the normal-ratio function field bound the actual Gauss dimension.
-/

namespace DimensionFourDependence

open Matrix Module

variable {F : Type*} [Field F]

/-- A nonzero kernel vector bounds a three-by-three matrix's rank by two. -/
theorem matrix_three_rank_le_two_of_nonzero_kernel
    (T : Matrix (Fin 3) (Fin 3) F) (u : Fin 3 → F) (hu : u ≠ 0) (hk : T *ᵥ u = 0) :
    T.rank ≤ 2 := by
  have hker : 0 < finrank F (LinearMap.ker T.toLin') := by
    apply (Module.finrank_pos_iff_exists_ne_zero (R := F) (M := LinearMap.ker T.toLin')).mpr
    exact ⟨⟨u, hk⟩, fun hz => hu (congrArg Subtype.val hz)⟩
  have hsum := LinearMap.finrank_range_add_finrank_ker T.toLin'
  have hr : finrank F (LinearMap.range T.toLin') = T.rank := rfl
  simp only [Module.finrank_pi, Fintype.card_fin] at hsum
  omega

variable {K : Type*} [Field K] [CharZero K]

omit [Field F] in
/-- Homogeneous weight one bounds the actual coefficient Hessian's rank. -/
theorem coefficientHessian_rank_le_two_of_euler
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (hh : coefficientEuler Y hY h = h) :
    (coefficientHessian Y hY h).rank ≤ 2 := by
  have hy : coefficientCoordinate (K := K) Y ≠ 0 := by
    intro hz
    apply (hY.transcendental 0).ne_zero
    have he := congrArg (fun z : coefficientField (K := K) Y =>
      (z : FractionRing (MvPolynomial (Fin 4) K))) (congrFun hz 0)
    exact he
  exact matrix_three_rank_le_two_of_nonzero_kernel (coefficientHessian Y hY h)
    (coefficientCoordinate (K := K) Y) hy
    (by simpa using coefficientHessian_radial_mulVec_map Y hY (coefficientField (K := K) Y) h hh)

omit [Field F] in
/-- The Gauss-image dimension bound for the original actual homogeneous
nilpotent rank-three map, without an assumed dimension of its image. -/
theorem gauss_image_dimension_le_two
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) : gaussImageDimension H I ≤ 2 := by
  obtain ⟨p, hY, h, c, q, k, hh, _, _, _⟩ := exists_three_fiber_invariants_polynomial H hN hrank
  rw [I.gauss_image_dimension_eq_hessian H p hY h hh]
  exact_mod_cast coefficientHessian_rank_le_two_of_euler _ hY h
    (homogeneous_last_output_euler H hd hH p hY h hh)

end DimensionFourDependence
