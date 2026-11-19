import DimensionFourDependence.GenericFiberPoleSeparation

/-! # The radial coordinate cannot have strictly greater pole order

The absence of the radial point from the actual projective closure
bounds its valuation by the other coordinates and one. This applies to
both branches of the quadratic fiber normal form in Section 3.2.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {E F : Type*} [Field E] [Field F] [Algebra E F] {n : ℕ}

/-- A strictly dominant radial coordinate would reduce to the excluded
radial point, so its value is bounded by the other two values and one. -/
theorem radial_coordinate_value_bound
    (x : Fin n → F) (Y Z W c : Fin n → E)
    (hY : (fun j : Option (Fin n) => j.elim 0 Y) ≠ 0)
    (hNoRadial : projectiveCoordinatePoint (fun j : Option (Fin n) => j.elim 0 Y) hY ∉
      projectiveClosureSet (L := E) x)
    (V : ValuationSubring F) [Algebra E V] [IsScalarTower E V F] (τ s t : F)
    (hx : ∀ i, x i = τ * algebraMap E F (Y i) + s * algebraMap E F (Z i) +
      t * algebraMap E F (W i) + algebraMap E F (c i)) :
    V.valuation τ ≤ max (max 1 (V.valuation s)) (V.valuation t) := by
  by_contra hn
  have hbig := lt_of_not_ge hn
  obtain ⟨h1s, ht⟩ := max_lt_iff.mp hbig
  obtain ⟨h1, hs⟩ := max_lt_iff.mp h1s
  let error : Fin n → F := fun i => s * algebraMap E F (Z i) +
    t * algebraMap E F (W i) + algebraMap E F (c i)
  have herr : ∀ i, V.valuation (error i) < V.valuation τ :=
    affine_isotropic_errors_below_radial V Z W c τ s t h1 hs ht
  have hx' (i : Fin n) : x i = τ * algebraMap E F (Y i) + error i := by
    rw [hx i]
    dsimp only [error]
    ring
  obtain ⟨z, hz, hres⟩ := dominant_radial_term_has_radial_residue V x error Y τ h1 herr hx'
  let κ := IsLocalRing.ResidueField V
  let π : V →ₐ[E] κ := IsScalarTower.toAlgHom E V κ
  have hmap : (fun j : Option (Fin n) => algebraMap E κ (j.elim 0 Y)) ≠ 0 := by
    intro he
    apply hY
    funext j
    apply (algebraMap E κ).injective
    simpa only [map_zero, Pi.zero_apply] using congrFun he j
  have hfun : (fun j => π (z j)) = fun j : Option (Fin n) => algebraMap E κ (j.elim 0 Y) := by
    funext j
    exact hres j
  have hnonzero : (fun j => π (z j)) ≠ 0 := by rw [hfun]; exact hmap
  have hp := residue_field_point_mem_projective_closure π
    (show Function.Injective (algebraMap V F) from Subtype.val_injective) x τ⁻¹ z hz hnonzero
  simp only [hfun, projectiveFieldPoint_map_eq _ hY] at hp
  exact hNoRadial hp

/-- At a pole of `s` where `t` is finite, the radial coordinate has
at most the pole order of `s`. -/
theorem radial_coordinate_value_le_single_pole
    (x : Fin n → F) (Y Z W c : Fin n → E)
    (hY : (fun j : Option (Fin n) => j.elim 0 Y) ≠ 0)
    (hNoRadial : projectiveCoordinatePoint (fun j : Option (Fin n) => j.elim 0 Y) hY ∉
      projectiveClosureSet (L := E) x)
    (V : ValuationSubring F) [Algebra E V] [IsScalarTower E V F] (τ s t : F)
    (hx : ∀ i, x i = τ * algebraMap E F (Y i) + s * algebraMap E F (Z i) +
      t * algebraMap E F (W i) + algebraMap E F (c i))
    (hs : 1 < V.valuation s) (ht : V.valuation t ≤ 1) : V.valuation τ ≤ V.valuation s := by
  have he := radial_coordinate_value_bound x Y Z W c hY hNoRadial V τ s t hx
  rw [max_eq_right hs.le, max_eq_left (ht.trans hs.le)] at he
  exact he

end DimensionFourDependence
