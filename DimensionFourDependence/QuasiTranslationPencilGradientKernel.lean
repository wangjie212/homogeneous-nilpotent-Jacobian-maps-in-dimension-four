import DimensionFourDependence.PrimitiveQuasiTranslationSourcePencil
import DimensionFourDependence.GenericReducedHomogeneousPencil
import DimensionFourDependence.CofinitePolynomialParameterKernel
import DimensionFourDependence.QuasiTranslationFiberDivisorTangency

/-! # The constructed source pencil gradients satisfy every original parameter coefficient equation -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 3000000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual primitive direction constructs an invariant reduced
homogeneous pencil whose two gradients lie in the scalar extension of
the original finite parameter coefficient kernel. All image-line
hypersurfaces, generic squarefreeness, degree comparisons and cofinite
parameter identities are constructed internally. -/
theorem primitive_positive_quasi_translation_constructs_source_pencil_gradient_coefficient_kernel
    (u : Fin 4 → R₀) {e : ℕ} (he : 0 < e) (hUne : u ≠ 0)
    (hhom : IsHomogMap u e) (hprim : IsPrimitiveVec u) (hacc : jac u *ᵥ u = 0) :
    ∃ (p q : R₀) (D : ℕ) (v : Fin 4 → Polynomial K) (t r : F₀),
      0 < D ∧ p ≠ 0 ∧ q ≠ 0 ∧ p.IsHomogeneous D ∧ q.IsHomogeneous D ∧ IsRelPrime p q ∧
      Transcendental K t ∧ r ≠ 0 ∧
      (∀ i, algebraMap R₀ F₀ (u i) = r * Polynomial.aeval t (v i)) ∧
      (polynomialCovectorCoefficientMatrix v).map (algebraMap K F₀) *ᵥ
        (fun i => algebraMap R₀ F₀ (pderiv i p)) = 0 ∧
      (polynomialCovectorCoefficientMatrix v).map (algebraMap K F₀) *ᵥ
        (fun i => algebraMap R₀ F₀ (pderiv i q)) = 0 := by
  obtain ⟨p, q, D, v, t, r, hD, hp, hq, hpH, hqH, hrel, ht, _htfrac,
    _hv, _hprimitive, hr, hrep, hDp, hDq, hmembers⟩ :=
    primitive_positive_quasi_translation_constructs_invariant_image_line_source_pencil
      u he hUne hhom hprim hacc
  obtain ⟨S, hS, hgood⟩ :=
    positive_homogeneous_reduced_pencil_constructs_finite_squarefree_exceptions p q hD hp hpH hqH hrel
  have hkernel (f : R₀) (hfH : f.IsHomogeneous D) (hf : polynomialVectorDerivation u f = 0) :
      (polynomialCovectorCoefficientMatrix v).map (algebraMap K F₀) *ᵥ
        (fun i => algebraMap R₀ F₀ (pderiv i f)) = 0 := by
    apply cofinite_parameter_incidence_mem_extended_coefficient_kernel v _ S hS
    intro a ha
    have hder : polynomialVectorDerivation (fun i => C ((v i).eval a)) f = 0 :=
      primitive_line_fiber_degree_bound_forces_invariant_constant_derivative_zero u hprim f hfH hf
        (p - C a * q) (hgood a ha).1 (fun i => (v i).eval a)
        (hmembers a).2.2.2.2 (by rw [(hgood a ha).2.2.2])
    have hC (c : K) : algebraMap R₀ F₀ (C c) = algebraMap K F₀ c :=
      (IsScalarTower.algebraMap_apply K R₀ F₀ c).symm
    have he := congrArg (algebraMap R₀ F₀) hder
    simpa only [polynomialVectorDerivation_apply, map_sum, map_mul, hC, map_zero] using he
  exact ⟨p, q, D, v, t, r, hD, hp, hq, hpH, hqH, hrel, ht, hr, hrep,
    hkernel p hpH hDp, hkernel q hqH hDq⟩

end DimensionFourDependence
