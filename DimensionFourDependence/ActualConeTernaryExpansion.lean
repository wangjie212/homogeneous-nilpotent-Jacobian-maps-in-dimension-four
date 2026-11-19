import DimensionFourDependence.ConeTernaryForms
import DimensionFourDependence.TangentMultipleSourceValue

/-! # Constructing the actual ternary expansion from the fixed-vertex cone form

The complete cone expression (4.7) and the constructed tangent multiple
give explicit forms of the original degree. Their values agree with all
four original coordinates at the actual projected source point. A
gradient version derives the required source-point multiple from the
actual affine fiber line and its base-point identity.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {F G : Type*} [Field F] [Field G] [Algebra F G]

/-- The fixed-vertex cone expression and its tangent multiple
construct the entire homogeneous ternary expansion, rather than
assuming the existence of any coordinate forms. -/
theorem cone_form_tangent_multiple_constructs_ternary_expansion
    {d : ℕ} (hd : 0 < d) (τ ν V : Fin 3 → F) (u a b : F)
    (z : Fin 3 → G) (r : G) (y : Fin 4 → G)
    (hr : r = algebraMap F G u * (∑ i, algebraMap F G (τ i) * z i))
    (hfirst : ∀ i : Fin 3, y i.castSucc = algebraMap F G (V i) * r ^ d)
    (hlast : y (Fin.last 3) = algebraMap F G a * r ^ d +
      algebraMap F G b * r ^ (d - 1) * (∑ i, algebraMap F G (ν i) * z i)) :
    (∀ i : Fin 4, (coneTernaryForms d τ ν V u a b i).IsHomogeneous d) ∧
      ∀ i : Fin 4, aeval z (coneTernaryForms d τ ν V u a b i) = y i := by
  obtain ⟨hfirstValue, hlastValue⟩ := coneTernaryForms_evaluate d τ ν V u a b z r hr
  refine ⟨coneTernaryForms_homogeneous hd τ ν V u a b, ?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact hlastValue.trans hlast.symm
  · exact (hfirstValue j).trans (hfirst j).symm

variable {K E : Type*} [Field K] [Field E] [Algebra K F] [Algebra K E]
    [Algebra F E] [Algebra E G] [IsScalarTower F E G] [IsScalarTower K F E]

/-- At the actual generic parabolic point, the finite tangent
multiplier and original homogeneous direction equation construct
the four homogeneous ternary forms with their exact source values.
No source-point tangent identity or coordinate expansion is supplied. -/
theorem cone_form_actual_gradient_multiple_constructs_ternary_expansion
    {d : ℕ} (hd : 0 < d) (A : Fin 3 → F) (Φ : MvPolynomial (Fin 3) K) {δ : ℕ}
    (hΦ : Φ.IsHomogeneous δ) (hzero : aeval A Φ = 0)
    (ν V : Fin 3 → F) (u a b : F) (x : Fin 3 → E) (t : G) (z : Fin 4 → G)
    (hz : ∀ i : Fin 3, z i.castSucc = algebraMap E G (x i) + algebraMap F G (A i) * t)
    (r : E) (y : Fin 4 → G)
    (hr : r = algebraMap F E u *
      (∑ i, aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) * x i))
    (hfirst : ∀ i : Fin 3, y i.castSucc = algebraMap F G (V i) * (algebraMap E G r) ^ d)
    (hlast : y (Fin.last 3) = algebraMap F G a * (algebraMap E G r) ^ d +
      algebraMap F G b * (algebraMap E G r) ^ (d - 1) *
        (∑ i : Fin 3, algebraMap F G (ν i) * z i.castSucc)) :
    ∃ P : Fin 4 → MvPolynomial (Fin 3) F, (∀ i, (P i).IsHomogeneous d) ∧
      ∀ i, aeval (fun j : Fin 3 => z j.castSucc) (P i) = y i := by
  have hsource := homogeneous_direction_tangent_multiple_actual_source_value
    A Φ hΦ hzero x t (fun i : Fin 3 => z i.castSucc) hz r u hr
  have hr' : algebraMap E G r = algebraMap F G u *
      (∑ i : Fin 3, algebraMap F G (aeval A (pderiv i Φ)) * z i.castSucc) := by
    simpa only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X] using hsource
  exact ⟨coneTernaryForms d (fun i => aeval A (pderiv i Φ)) ν V u a b,
    cone_form_tangent_multiple_constructs_ternary_expansion hd _ ν V u a b _ _ y hr' hfirst hlast⟩

end DimensionFourDependence
