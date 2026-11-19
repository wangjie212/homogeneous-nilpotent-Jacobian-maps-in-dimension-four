import DimensionFourDependence.RadialBoundaryEquations
import DimensionFourDependence.ExtensionFieldProjectivePoint

/-! # The primitive map sends a boundary direction to its projective target

The original homogeneous cross equations specialize at arbitrary
extension-field points of the actual fiber closure. Wherever P is
defined, its value is a nonzero scalar multiple of the fiber target.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {E F κ : Type*} [Field E] [Field F] [Field κ] [Algebra E F] [Algebra E κ]

/-- Original homogeneous closure equations hold at extension-field
coordinates, with no identification of the residue field and constants. -/
theorem projectiveClosureSet_extension_coordinate_equation {σ : Type*}
    (x : σ → F) (z : Option σ → κ) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := E) z hz ∈ projectiveClosureSet (L := E) x)
    {p : MvPolynomial (Option σ) E} {d : ℕ} (hp : p.IsHomogeneous d)
    (hvan : p ∈ projectiveConeIdeal (L := E) x) : aeval z p = 0 := by
  have hc : projectiveClosureSet (L := E) x =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option σ) E)
        (projectiveConeIdeal (L := E) x : Set (MvPolynomial (Option σ) E)) := by
    change closure {projectiveClosureGenericPoint (L := E) x} =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option σ) E)
        ((projectiveClosureGenericPoint (L := E) x).asHomogeneousIdeal : Set _)
    rw [← ProjectiveSpectrum.vanishingIdeal_singleton]
    exact (ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure _ _).symm
  rw [hc] at hpoint
  have he := hpoint hvan
  change projectiveFieldPointMap (E := E) z p = 0 at he
  rwa [projectiveFieldPointMap_homogeneous z hp, Polynomial.monomial_eq_zero_iff] at he

/-- Every extension-field direction on the actual projective fiber
closure satisfies the original primitive-map cross equations. -/
theorem primitive_boundary_cross_equations
    (H P : Fin 4 → MvPolynomial (Fin 4) E) (g : MvPolynomial (Fin 4) E)
    {D : ℕ} (hP : IsHomogMap P D) (hHP : H = fun i => g * P i)
    (x : Fin 4 → F) (y : Fin 4 → E) (hy : y ≠ 0)
    (hHx : ∀ i, aeval x (H i) = algebraMap E F (y i))
    (z : Option (Fin 4) → κ) (hz : z ≠ 0)
    (hboundary : projectiveFieldPoint (E := E) z hz ∈ projectiveClosureSet (L := E) x) :
    ∀ i j, algebraMap E κ (y i) * aeval (fun k => z (some k)) (P j) -
      algebraMap E κ (y j) * aeval (fun k => z (some k)) (P i) = 0 := by
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
  have hq : q.IsHomogeneous D := ((hP j).C_mul (y i)).sub ((hP i).C_mul (y j))
  have hqx : aeval x q = 0 := by
    apply mul_left_cancel₀ hg
    simp only [q, map_sub, map_mul, aeval_C, mul_zero]
    linear_combination (algebraMap E F (y i)) * hval j - (algebraMap E F (y j)) * hval i
  have hcone : rename some q ∈ projectiveConeIdeal (L := E) x := by
    apply (projectiveConeIdeal_mem_of_isHomogeneous x hq.rename_isHomogeneous).mpr
    simpa only [aeval_rename, Function.comp_def, Option.elim_some] using hqx
  have he := projectiveClosureSet_extension_coordinate_equation x z hz hboundary hq.rename_isHomogeneous hcone
  simpa only [aeval_rename, Function.comp_def, q, map_sub, map_mul, aeval_C] using he

omit [Field E] [Field F] [Algebra E F] [Algebra E κ] in
/-- The actual homogeneous cross equations identify nonzero vectors
up to a nonzero scalar, over any field. -/
theorem nonzero_vectors_proportional_of_cross_equations {n : ℕ}
    (y u : Fin n → κ) (hy : y ≠ 0) (hu : u ≠ 0)
    (hcross : ∀ i j, y i * u j - y j * u i = 0) :
    ∃ c : κ, c ≠ 0 ∧ ∀ i, u i = c * y i := by
  obtain ⟨a, ha⟩ : ∃ a, y a ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hy
  let c := u a / y a
  have he (i : Fin n) : u i = c * y i := by
    have h := hcross a i
    dsimp only [c]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff ha).mpr
    linear_combination h
  have hc : c ≠ 0 := by
    intro hz
    apply hu
    funext i
    simpa only [hz, zero_mul, Pi.zero_apply] using he i
  exact ⟨c, hc, he⟩

/-- Wherever the primitive part is defined, every actual boundary
point maps to the original fiber's projective target, even over a
larger residue field. -/
theorem primitive_boundary_image_proportional_to_target
    (H P : Fin 4 → MvPolynomial (Fin 4) E) (g : MvPolynomial (Fin 4) E)
    {D : ℕ} (hP : IsHomogMap P D) (hHP : H = fun i => g * P i)
    (x : Fin 4 → F) (y : Fin 4 → E) (hy : y ≠ 0)
    (hHx : ∀ i, aeval x (H i) = algebraMap E F (y i))
    (z : Option (Fin 4) → κ) (hz : z ≠ 0)
    (hboundary : projectiveFieldPoint (E := E) z hz ∈ projectiveClosureSet (L := E) x)
    (hPz : (fun i => aeval (fun k => z (some k)) (P i)) ≠ 0) :
    ∃ c : κ, c ≠ 0 ∧ ∀ i, aeval (fun k => z (some k)) (P i) = c * algebraMap E κ (y i) := by
  apply nonzero_vectors_proportional_of_cross_equations _ _ _ hPz
    (primitive_boundary_cross_equations H P g hP hHP x y hy hHx z hz hboundary)
  intro he
  apply hy
  funext i
  change y i = 0
  apply (algebraMap E κ).injective
  simpa only [map_zero, Pi.zero_apply] using congrFun he i

end DimensionFourDependence
