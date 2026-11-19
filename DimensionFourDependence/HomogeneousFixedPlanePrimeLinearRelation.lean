import DimensionFourDependence.FixedPlaneProjectionPolynomial
import DimensionFourDependence.HomogeneousBinaryDehomogenization
import DimensionFourDependence.GeneratedPointPrimeDimension

/-! # A homogeneous fixed-plane equation in a prime gives an original constant linear form -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 3000000

variable {K E : Type u} [Field K] [Field E] [Algebra K E]

/-- A nonzero homogeneous binary equation makes the actual affine
ratio algebraic wherever its second coordinate is nonzero. -/
theorem homogeneous_binary_root_second_coordinate_ratio_isAlgebraic
    (a : MvPolynomial (Fin 2) K) {N : ℕ} (ha : a.IsHomogeneous N) (ha0 : a ≠ 0)
    (x y : E) (hy : y ≠ 0) (hroot : aeval ![x, y] a = 0) : IsAlgebraic K (x / y) := by
  obtain ⟨v, hvN, hvHom⟩ := homogeneous_binary_form_constructs_bounded_univariate_parameter a ha
  have hv : v ≠ 0 := by
    intro hz
    apply ha0
    rw [← hvHom, hz, Polynomial.homogenize_zero]
  have hvalue : homogeneousParameterPolynomialValue v N x y = 0 := by
    rw [homogeneousParameterPolynomialValue, hvHom]
    exact hroot
  rw [homogeneousParameterPolynomialValue_fraction v hvN x y hy] at hvalue
  exact ⟨v, hv, (mul_eq_zero.mp hvalue).resolve_left (pow_ne_zero N hy)⟩

variable [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "A₀" => MvPolynomial (Fin 2) K

omit [Field E] [Algebra K E] in
/-- A nonzero homogeneous equation in the two fixed original
coordinates, contained in an actual source prime, constructs a
nonzero original constant linear form in that same prime. No closed
point or chosen prime factor of the binary equation is supplied. -/
theorem homogeneous_fixed_plane_equation_in_prime_constructs_constant_linear_form
    (P : Ideal R₀) [P.IsPrime] (a : A₀) {N : ℕ} (ha : a.IsHomogeneous N)
    (ha0 : a ≠ 0) (haP : fixedPlaneCoefficientMap K a ∈ P) :
    ∃ α β : K, (α ≠ 0 ∨ β ≠ 0) ∧ C α * X 0 + C β * X 3 ∈ P := by
  classical
  let L := FractionRing (R₀ ⧸ P)
  let f : R₀ →ₐ[K] L := IsScalarTower.toAlgHom K R₀ L
  have hzero (r : R₀) : f r = 0 ↔ r ∈ P := by
    change r ∈ RingHom.ker (algebraMap R₀ L) ↔ r ∈ P
    rw [prime_quotient_fraction_algebraMap_ker]
  let x : L := f (X 0)
  let y : L := f (X 3)
  have hcomp : f.comp (fixedPlaneCoefficientMap K) = aeval (![x, y] : Fin 2 → L) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [fixedPlaneCoefficientMap, x, y]
  have hroot : aeval (![x, y] : Fin 2 → L) a = 0 :=
    (AlgHom.congr_fun hcomp a).symm.trans ((hzero _).mpr haP)
  by_cases hy : y = 0
  · refine ⟨0, 1, Or.inr one_ne_zero, ?_⟩
    have hX3 : X (3 : Fin 4) ∈ P := (hzero _).mp hy
    simpa only [map_zero, map_one, zero_mul, one_mul, zero_add] using hX3
  · have halg := homogeneous_binary_root_second_coordinate_ratio_isAlgebraic a ha ha0 x y hy hroot
    have hmem : x / y ∈ algebraicClosure K L := mem_algebraicClosure_iff.mpr halg
    have hbot : algebraicClosure K L = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
    rw [hbot] at hmem
    obtain ⟨c, hc⟩ : ∃ c : K, algebraMap K L c = x / y := hmem
    have hC (c : K) : f (C c) = algebraMap K L c := f.commutes c
    have hlinear : f (X 0 - C c * X 3) = 0 := by
      rw [map_sub, map_mul, hC]
      change x - algebraMap K L c * y = 0
      rw [hc, div_mul_cancel₀ _ hy, sub_self]
    refine ⟨1, -c, Or.inl one_ne_zero, ?_⟩
    have hmem := (hzero _).mp hlinear
    simpa only [map_one, one_mul, map_neg, neg_mul, ← sub_eq_add_neg] using hmem

end DimensionFourDependence
