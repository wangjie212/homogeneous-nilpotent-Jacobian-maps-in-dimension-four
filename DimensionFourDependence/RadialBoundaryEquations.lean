import DimensionFourDependence.ProjectiveCoordinatePoint

/-! # Homogeneous equations specialize at a fiber's infinity directions

For `H = g P`, the homogeneous equations `yᵢ Pⱼ − yⱼ Pᵢ` vanish on
the nonzero fiber over `y`. Their vanishing persists on its actual
projective closure, so the radial infinity point forces `P(y)` to be
radial. No choice of normalization or local parameter is needed.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

/-- Homogeneous projective-fiber equations persist at an infinity point
of the closure of any affine point over a nonzero value. -/
theorem radial_boundary_cross_equations
    (H P : Fin 4 → MvPolynomial (Fin 4) E) (g : MvPolynomial (Fin 4) E)
    {a : ℕ} (hP : IsHomogMap P a) (hHP : H = fun i => g * P i)
    (x : Fin 4 → F) (y : Fin 4 → E) (hy : y ≠ 0)
    (hHx : ∀ i, aeval x (H i) = algebraMap E F (y i))
    (hz : (fun j : Option (Fin 4) => j.elim 0 y) ≠ 0)
    (hboundary : projectiveCoordinatePoint (fun j : Option (Fin 4) => j.elim 0 y) hz ∈
      projectiveClosureSet (L := E) x) :
    ∀ i j, y i * aeval y (P j) - y j * aeval y (P i) = 0 := by
  classical
  have hg : aeval x g ≠ 0 := by
    intro hg
    apply hy
    funext i
    change y i = 0
    apply (algebraMap E F).injective
    rw [map_zero, ← hHx i, congrFun hHP i, map_mul, hg, zero_mul]
  have hval (i : Fin 4) : aeval x g * aeval x (P i) = algebraMap E F (y i) := by
    rw [← map_mul, ← congrFun hHP i, hHx i]
  intro i j
  let q : MvPolynomial (Fin 4) E := C (y i) * P j - C (y j) * P i
  have hq : q.IsHomogeneous a :=
    ((hP j).C_mul (y i)).sub ((hP i).C_mul (y j))
  have hqx : aeval x q = 0 := by
    apply mul_left_cancel₀ hg
    simp only [q, map_sub, map_mul, aeval_C, mul_zero]
    linear_combination (algebraMap E F (y i)) * hval j -
      (algebraMap E F (y j)) * hval i
  have hcone : rename some q ∈ projectiveConeIdeal (L := E) x := by
    apply (projectiveConeIdeal_mem_of_isHomogeneous x hq.rename_isHomogeneous).mpr
    simpa only [aeval_rename, Function.comp_def, Option.elim_some] using hqx
  have hb := projectiveClosureSet_coordinate_equation x
    (fun k : Option (Fin 4) => k.elim 0 y) hz hboundary hq.rename_isHomogeneous hcone
  simpa only [aeval_rename, Function.comp_def, Option.elim_some, q,
    map_sub, map_mul, aeval_C, Algebra.algebraMap_self_apply] using hb

end DimensionFourDependence
