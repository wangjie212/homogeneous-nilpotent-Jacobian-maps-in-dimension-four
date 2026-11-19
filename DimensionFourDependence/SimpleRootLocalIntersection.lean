import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-! # The local algebra of a simple root on a doubled line

In a local algebra, u^2=0 and a quadratic equation with nonzero
linear v coefficient force uv=v^2=0 and express v as a scalar multiple
of u. When u,v generate the maximal ideal and the closed point has the
original residue field, the algebra is spanned by 1,u. Its dimension
and its module length are at most two.

This proves the local algebra estimate used in Section 4.3. Realizing
the actual projective fiber intersection in this local model remains
separate.
-/

namespace DimensionFourDependence

open Module

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A] [IsLocalRing A]

/-- A quadratic simple-root equation on a doubled line eliminates
the second local coordinate, retaining its nilpotent relations. -/
theorem simple_root_double_line_local_relations
    (u v : A) (hu : u ∈ IsLocalRing.maximalIdeal A) (hv : v ∈ IsLocalRing.maximalIdeal A)
    (a b c e f : F) (hb : b ≠ 0) (hu2 : u ^ 2 = 0)
    (hG : algebraMap F A a * u + algebraMap F A b * v + algebraMap F A c * u ^ 2 +
      algebraMap F A e * u * v + algebraMap F A f * v ^ 2 = 0) :
    u * v = 0 ∧ v ^ 2 = 0 ∧ v = algebraMap F A (-a / b) * u := by
  let T : A := algebraMap F A b + algebraMap F A e * u + algebraMap F A f * v
  have htail : algebraMap F A e * u + algebraMap F A f * v ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.maximalIdeal A).add_mem
      ((IsLocalRing.maximalIdeal A).mul_mem_left _ hu) ((IsLocalRing.maximalIdeal A).mul_mem_left _ hv)
  have hbunit : IsUnit (algebraMap F A b) := (isUnit_iff_ne_zero.mpr hb).map (algebraMap F A)
  have hT : IsUnit T := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hmem
    have he := (IsLocalRing.maximalIdeal A).sub_mem hmem htail
    have he' : algebraMap F A b ∈ IsLocalRing.maximalIdeal A := by
      convert he using 1
      dsimp [T]
      ring
    exact (IsLocalRing.notMem_maximalIdeal.mpr hbunit) he'
  have he : algebraMap F A a * u + T * v = 0 := by
    dsimp [T]
    linear_combination hG - algebraMap F A c * hu2
  have huv : u * v = 0 := by
    apply hT.mul_left_cancel
    rw [mul_zero]
    linear_combination u * he - algebraMap F A a * hu2
  have hv2 : v ^ 2 = 0 := by
    apply hT.mul_left_cancel
    rw [mul_zero]
    linear_combination v * he - algebraMap F A a * huv
  have hlinear : algebraMap F A a * u + algebraMap F A b * v = 0 := by
    linear_combination hG - algebraMap F A c * hu2 - algebraMap F A e * huv - algebraMap F A f * hv2
  refine ⟨huv, hv2, ?_⟩
  have hinv : algebraMap F A b⁻¹ * algebraMap F A b = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hb, map_one]
  have hcoef : algebraMap F A (-a / b) = -(algebraMap F A b⁻¹ * algebraMap F A a) := by
    simp only [div_eq_mul_inv, map_mul, map_neg]
    ring
  rw [hcoef]
  linear_combination algebraMap F A b⁻¹ * hlinear - v * hinv

/-- A square-zero principal maximal ideal and unchanged residue field
give an explicit two-term scalar expression for every element. -/
theorem square_zero_principal_local_algebra_expression
    (u : A) (hu2 : u ^ 2 = 0)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span ({u} : Set A))
    (hres : Function.Surjective (algebraMap F (A ⧸ IsLocalRing.maximalIdeal A))) :
    ∀ z : A, ∃ a b : F, z = algebraMap F A a + algebraMap F A b * u := by
  intro z
  have hrep (x : A) : ∃ a : F, ∃ b : A, x = algebraMap F A a + b * u := by
    obtain ⟨a, ha⟩ := hres (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) x)
    have hx : x - algebraMap F A a ∈ IsLocalRing.maximalIdeal A := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub]
      change Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) x -
        algebraMap F (A ⧸ IsLocalRing.maximalIdeal A) a = 0
      rw [ha, sub_self]
    rw [hmax, Ideal.mem_span_singleton'] at hx
    obtain ⟨b, hb⟩ := hx
    exact ⟨a, b, by linear_combination -hb⟩
  obtain ⟨a, q, hz⟩ := hrep z
  obtain ⟨b, r, hq⟩ := hrep q
  refine ⟨a, b, ?_⟩
  rw [hz, hq]
  linear_combination r * hu2

/-- The local simple-root intersection algebra is spanned by 1,u. -/
theorem simple_root_double_line_local_span
    (u v : A) (hu : u ∈ IsLocalRing.maximalIdeal A) (hv : v ∈ IsLocalRing.maximalIdeal A)
    (a b c e f : F) (hb : b ≠ 0) (hu2 : u ^ 2 = 0)
    (hG : algebraMap F A a * u + algebraMap F A b * v + algebraMap F A c * u ^ 2 +
      algebraMap F A e * u * v + algebraMap F A f * v ^ 2 = 0)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span ({u, v} : Set A))
    (hres : Function.Surjective (algebraMap F (A ⧸ IsLocalRing.maximalIdeal A))) :
    Submodule.span F (Set.range ![(1 : A), u]) = ⊤ := by
  have hrel := (simple_root_double_line_local_relations u v hu hv a b c e f hb hu2 hG).2.2
  have hmax' : IsLocalRing.maximalIdeal A = Ideal.span ({u} : Set A) := by
    rw [hmax]
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro z (rfl | rfl)
      · exact Ideal.subset_span (by simp)
      · rw [hrel]
        exact (Ideal.span ({u} : Set A)).mul_mem_left _ (Ideal.subset_span (by simp))
    · apply Ideal.span_mono
      intro x hx
      simp only [Set.mem_singleton_iff, Set.mem_insert_iff] at hx ⊢
      exact Or.inl hx
  apply top_unique
  intro z _
  obtain ⟨alpha, beta, hz⟩ := square_zero_principal_local_algebra_expression u hu2 hmax' hres z
  rw [hz]
  apply Submodule.add_mem
  · have h1 : (1 : A) ∈ Submodule.span F (Set.range ![(1 : A), u]) := Submodule.subset_span ⟨0, rfl⟩
    simpa only [Algebra.smul_def, mul_one] using
      (Submodule.span F (Set.range ![(1 : A), u])).smul_mem alpha h1
  · have hU : u ∈ Submodule.span F (Set.range ![(1 : A), u]) := Submodule.subset_span ⟨1, rfl⟩
    simpa only [Algebra.smul_def] using
      (Submodule.span F (Set.range ![(1 : A), u])).smul_mem beta hU

/-- The local algebra estimate for the doubled-line simple-root
intersection, including its module length bound. -/
theorem simple_root_double_line_local_dimension_and_length_le_two
    (u v : A) (hu : u ∈ IsLocalRing.maximalIdeal A) (hv : v ∈ IsLocalRing.maximalIdeal A)
    (a b c e f : F) (hb : b ≠ 0) (hu2 : u ^ 2 = 0)
    (hG : algebraMap F A a * u + algebraMap F A b * v + algebraMap F A c * u ^ 2 +
      algebraMap F A e * u * v + algebraMap F A f * v ^ 2 = 0)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span ({u, v} : Set A))
    (hres : Function.Surjective (algebraMap F (A ⧸ IsLocalRing.maximalIdeal A))) :
    Module.Finite F A ∧ finrank F A ≤ 2 ∧ Module.length A A ≤ 2 := by
  have hspan := simple_root_double_line_local_span u v hu hv a b c e f hb hu2 hG hmax hres
  have hdim : finrank F A ≤ 2 := by
    simpa only [Fintype.card_fin] using finrank_le_of_span_eq_top hspan
  have hfinite : Module.Finite F A := by
    apply Module.Finite.of_fg_top
    rw [← hspan]
    exact Submodule.fg_span (Set.finite_range _)
  let := hfinite
  refine ⟨hfinite, hdim, ?_⟩
  have hlen := (⊤ : Submodule A A).length_le_length_restrictScalars F
  rw [Module.length_top, Submodule.restrictScalars_top, Module.length_top,
    Module.length_eq_finrank] at hlen
  exact hlen.trans (by exact_mod_cast hdim)

/-- If the doubled-line coordinate survives, the local intersection
has length exactly two, with no reducedness assumption. -/
theorem simple_root_double_line_local_length_eq_two
    (u v : A) (hu : u ∈ IsLocalRing.maximalIdeal A) (hv : v ∈ IsLocalRing.maximalIdeal A)
    (a b c e f : F) (hb : b ≠ 0) (hu2 : u ^ 2 = 0) (hu0 : u ≠ 0)
    (hG : algebraMap F A a * u + algebraMap F A b * v + algebraMap F A c * u ^ 2 +
      algebraMap F A e * u * v + algebraMap F A f * v ^ 2 = 0)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span ({u, v} : Set A))
    (hres : Function.Surjective (algebraMap F (A ⧸ IsLocalRing.maximalIdeal A))) :
    Module.length A A = 2 := by
  have hbound := simple_root_double_line_local_dimension_and_length_le_two u v hu hv a b c e f hb hu2 hG hmax hres
  apply le_antisymm hbound.2.2
  let m := IsLocalRing.maximalIdeal A
  have hune : (⟨u, hu⟩ : m) ≠ 0 := by
    intro he
    exact hu0 (congrArg Subtype.val he)
  let : Nontrivial m := nontrivial_of_ne (⟨u, hu⟩ : m) 0 hune
  have hm : 1 ≤ Module.length A m := Order.one_le_iff_pos.mpr Module.length_pos
  have hq : 1 ≤ Module.length A (A ⧸ m) := Order.one_le_iff_pos.mpr Module.length_pos
  have he := Module.length_eq_add_of_exact m.subtype m.mkQ m.subtype_injective m.mkQ_surjective
    (LinearMap.exact_subtype_mkQ m)
  rw [he]
  calc
    (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ Module.length A m + Module.length A (A ⧸ m) := add_le_add hm hq

end DimensionFourDependence
