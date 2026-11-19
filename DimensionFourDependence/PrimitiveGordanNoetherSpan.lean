import DimensionFourDependence.QuasiTranslationPencilGradientKernel
import DimensionFourDependence.HomogeneousPencilGradientIndependence
import DimensionFourDependence.SmallKernelScalarExtension

/-! # The primitive four-variable Gordan-Noether span bound

The constructed homogeneous pencil supplies two independent extended
solutions of the finite original parameter coefficient kernel. A
one-dimensional original kernel could not contain them after scalar
extension. Its two constructed original constant relations transfer
to the actual polynomial direction and give the required span bound.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

universe u
set_option maxHeartbeats 3000000

section LinearAlgebra

variable {K E : Type*} [Field K] [Field E] [Algebra K E] {m n : ℕ}

/-- Two independent solutions after scalar extension force two
original constant kernel dimensions. No extended rank equality is assumed. -/
theorem independent_extended_kernel_pair_forces_two_original_kernel_dimensions
    (A : Matrix (Fin m) (Fin n) K) (p q : Fin n → E)
    (hli : LinearIndependent E ![p, q])
    (hp : A.map (algebraMap K E) *ᵥ p = 0) (hq : A.map (algebraMap K E) *ᵥ q = 0) :
    2 ≤ finrank K (LinearMap.ker A.toLin') := by
  by_contra hn
  obtain ⟨c, _hc, hgen⟩ := matrix_kernel_finrank_le_one_constant_generator (E := E) A (by omega)
  obtain ⟨a, ha⟩ := hgen p hp
  obtain ⟨b, hb⟩ := hgen q hq
  have hrel : b • p + (-a) • q = 0 := by
    rw [ha, hb, smul_smul, smul_smul]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring
  have hz := (LinearIndependent.pair_iff.mp hli) b (-a) hrel
  have ha0 : a = 0 := neg_eq_zero.mp hz.2
  have hp0 : p = 0 := by rw [ha, ha0, zero_smul]
  have hpne : p ≠ 0 := by simpa only [Matrix.cons_val_zero] using hli.ne_zero 0
  exact hpne hp0

end LinearAlgebra

variable {K : Type u} [Field K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- Every original constant relation of the actual polynomial
parameter coefficients transfers to the original polynomial vector. -/
theorem parameter_coefficient_kernel_relation_transfers_to_original_vector
    (u : Fin 4 → R₀) (v : Fin 4 → Polynomial K) (t r : F₀)
    (hrep : ∀ i, algebraMap R₀ F₀ (u i) = r * Polynomial.aeval t (v i))
    (c : Fin 4 → K) (hc : polynomialCovectorCoefficientMatrix v *ᵥ c = 0) :
    (∑ i, c i • u i) = 0 := by
  have hpoly := (polynomial_covector_coefficient_kernel_iff v c).mp hc
  have hvalue : (∑ i, algebraMap K F₀ (c i) * Polynomial.aeval t (v i)) = 0 := by
    have he := congrArg (Polynomial.aeval t) hpoly
    simpa only [map_sum, map_mul, Polynomial.aeval_C, map_zero] using he
  have hC (a : K) : algebraMap R₀ F₀ (C a) = algebraMap K F₀ a :=
    (IsScalarTower.algebraMap_apply K R₀ F₀ a).symm
  apply IsFractionRing.injective R₀ F₀
  simp only [MvPolynomial.smul_eq_C_mul, map_sum, map_mul, hC, map_zero]
  simp_rw [hrep]
  calc
    (∑ i, algebraMap K F₀ (c i) * (r * Polynomial.aeval t (v i))) =
        r * ∑ i, algebraMap K F₀ (c i) * Polynomial.aeval t (v i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [hvalue, mul_zero]

/-- Two independent actual constant relations bound the original
component span by two, using the actual polynomial linear-combination map. -/
theorem two_independent_constant_relations_bound_component_span
    (u : Fin 4 → R₀) (r s : Fin 4 → K) (hli : LinearIndependent K ![r, s])
    (hr : (∑ i, r i • u i) = 0) (hs : (∑ i, s i • u i) = 0) :
    finrank K (Submodule.span K (Set.range u)) ≤ 2 := by
  let L := Fintype.linearCombination K u
  let cr : LinearMap.ker L := ⟨r, hr⟩
  let cs : LinearMap.ker L := ⟨s, hs⟩
  have hliK : LinearIndependent K ![cr, cs] := by
    apply LinearIndependent.of_comp (LinearMap.ker L).subtype
    convert hli using 1
    funext i
    fin_cases i <;> rfl
  have hbound := hliK.fintype_card_le_finrank
  have hdim := LinearMap.finrank_range_add_finrank_ker L
  have hrange : finrank K (LinearMap.range L) = finrank K (Submodule.span K (Set.range u)) := by
    rw [Fintype.range_linearCombination]
  rw [hrange] at hdim
  simp only [Fintype.card_fin, Module.finrank_pi] at hbound hdim
  omega

variable [CharZero K] [IsAlgClosed K]

/-- The actual primitive positive homogeneous four-variable
quasi-translation constructs two independent original constant component
relations. The rational parameter, invariant hypersurfaces, finite
squarefree exception set and independent pencil gradients are all derived. -/
theorem primitive_positive_homogeneous_quasi_translation_constructs_two_constant_relations
    (u : Fin 4 → R₀) {e : ℕ} (he : 0 < e) (hUne : u ≠ 0)
    (hhom : IsHomogMap u e) (hprim : IsPrimitiveVec u) (hacc : jac u *ᵥ u = 0) :
    ∃ r s : Fin 4 → K, LinearIndependent K ![r, s] ∧
      (∑ i, r i • u i) = 0 ∧ (∑ i, s i • u i) = 0 := by
  obtain ⟨p, q, D, v, t, r, hD, hp, hq, hpH, hqH, hrel, _ht, _hr, hrep, hkp, hkq⟩ :=
    primitive_positive_quasi_translation_constructs_source_pencil_gradient_coefficient_kernel
      u he hUne hhom hprim hacc
  have hli := positive_reduced_homogeneous_source_pencil_gradients_independent p q hD hp hq hpH hqH hrel
  let A := polynomialCovectorCoefficientMatrix v
  have hdim : 2 ≤ finrank K (LinearMap.ker A.toLin') :=
    independent_extended_kernel_pair_forces_two_original_kernel_dimensions A _ _ hli hkp hkq
  obtain ⟨w, hw⟩ := exists_linearIndependent_of_le_finrank hdim
  have hwi : LinearIndependent K (fun i : Fin 2 => (w i : Fin 4 → K)) :=
    hw.map' (f := (LinearMap.ker A.toLin').subtype) (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have heq : (fun i : Fin 2 => (w i : Fin 4 → K)) = ![(w 0 : Fin 4 → K), (w 1 : Fin 4 → K)] := by
    funext i
    fin_cases i <;> rfl
  rw [heq] at hwi
  exact ⟨w 0, w 1, hwi,
    parameter_coefficient_kernel_relation_transfers_to_original_vector u v t r hrep (w 0) (w 0).property,
    parameter_coefficient_kernel_relation_transfers_to_original_vector u v t r hrep (w 1) (w 1).property⟩

/-- The primitive positive four-variable Gordan-Noether bound:
the actual component span of the homogeneous quasi-translation has
dimension at most two. No classification theorem, span bound, parameter,
line fiber data or coordinate choice is supplied as a hypothesis. -/
theorem primitive_positive_homogeneous_quasi_translation_component_span_at_most_two
    (u : Fin 4 → R₀) {e : ℕ} (he : 0 < e) (hUne : u ≠ 0)
    (hhom : IsHomogMap u e) (hprim : IsPrimitiveVec u) (hacc : jac u *ᵥ u = 0) :
    finrank K (Submodule.span K (Set.range u)) ≤ 2 := by
  obtain ⟨r, s, hli, hr, hs⟩ :=
    primitive_positive_homogeneous_quasi_translation_constructs_two_constant_relations u he hUne hhom hprim hacc
  exact two_independent_constant_relations_bound_component_span u r s hli hr hs

end DimensionFourDependence
