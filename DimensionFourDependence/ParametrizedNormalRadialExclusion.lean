import DimensionFourDependence.RationalIncidenceSection
import DimensionFourDependence.NormalSpanDependence
import DimensionFourDependence.GaussNormalChart

/-! # The zero-radial-pairing obstruction from a primitive rational normal parameter

The primitive rational parameter presentation is explicit in this module;
constructing it from the actual one-dimensional Gauss image is separate.
The rational-section argument forces its covector entries to be linear.
The actual polynomial normal then has constant component span at most two,
which supplies the checked original-field component dependence conclusion.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

/-- A polynomial vector whose actual fraction-field values lie in the
span of two fixed rational scalars has constant component span at most two
already in the original polynomial ring. -/
theorem polynomial_component_span_le_two_of_fraction_presentation
    (N : Fin n → MvPolynomial (Fin n) K)
    (s t : FractionRing (MvPolynomial (Fin n) K)) (a b : Fin n → K)
    (he : ∀ i, algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (N i) =
      algebraMap K (FractionRing (MvPolynomial (Fin n) K)) (a i) * s +
        algebraMap K (FractionRing (MvPolynomial (Fin n) K)) (b i) * t) :
    finrank K (Submodule.span K (Set.range N)) ≤ 2 := by
  classical
  let f := (IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K)
    (FractionRing (MvPolynomial (Fin n) K))).toLinearMap
  have hf : Function.Injective f := IsFractionRing.injective _ _
  let U := Submodule.span K (Set.range N)
  let V := Submodule.span K (Set.range (![s, t] : Fin 2 → FractionRing (MvPolynomial (Fin n) K)))
  let : Module.Finite K V := Module.Finite.span_of_finite K (Set.finite_range _)
  have hm : U.map f ≤ V := by
    apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change f (N i) ∈ V
    change algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (N i) ∈ V
    rw [he i]
    have hs : s ∈ V := Submodule.subset_span ⟨0, rfl⟩
    have ht : t ∈ V := Submodule.subset_span ⟨1, rfl⟩
    simpa only [Algebra.smul_def] using V.add_mem (V.smul_mem (a i) hs) (V.smul_mem (b i) ht)
  have hV : finrank K V ≤ 2 := by
    simpa only [Set.finrank, V, Fintype.card_fin] using (finrank_range_le_card (R := K)
      (![s, t] : Fin 2 → FractionRing (MvPolynomial (Fin n) K)))
  exact ((Submodule.equivMapOfInjective f hf U).finrank_eq.trans_le (Submodule.finrank_mono hm)).trans hV

variable [CharZero K]

/-- Under a primitive actual rational parameter presentation of the
image normal, zero pairing with the actual source vector forces an
original-field constant relation among the homogeneous map components.
No degree or linearity of the parameter covector is assumed. -/
theorem dependence_of_parametrized_zero_radial_image_normal
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (I : ImageRelationWitness H)
    (v : Fin 4 → Polynomial K) (hv : v ≠ 0)
    (hprimitive : ∀ r : Polynomial K, (∀ i, r ∣ v i) → IsUnit r)
    (t c : FractionRing (MvPolynomial (Fin 4) K))
    (hrep : ∀ i, rationalImageNormal H I.equation i = c * Polynomial.aeval t (v i))
    (hradial : ∑ i, rationalImageNormal H I.equation i * rationalCoordinate (K := K) i = 0) :
    ComponentsDependent H := by
  have hc : c ≠ 0 := by
    intro hz
    apply I.normal_ne_zero
    funext i
    apply IsFractionRing.injective (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
    simpa only [hz, zero_mul, rationalImageNormal, map_zero, Pi.zero_apply] using hrep i
  have hsection : ∑ i, Polynomial.aeval t (v i) * rationalCoordinate (K := K) i = 0 := by
    apply (mul_eq_zero.mp (show c * (∑ i, Polynomial.aeval t (v i) * rationalCoordinate (K := K) i) = 0 from ?_)).resolve_left hc
    calc
      _ = ∑ i, rationalImageNormal H I.equation i * rationalCoordinate (K := K) i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hrep i]
        ring
      _ = 0 := hradial
  have hdegree := primitive_covector_natDegree_le_one_of_rational_section v hv hprimitive t hsection
  have heval (i : Fin 4) : Polynomial.aeval t (v i) =
      algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) ((v i).coeff 1) * t +
        algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) ((v i).coeff 0) := by
    have he := congrArg (Polynomial.aeval t) (Polynomial.eq_X_add_C_of_natDegree_le_one (hdegree i))
    simpa only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X] using he
  have hspan : finrank K (Submodule.span K (Set.range (imageRelationNormal H I.equation))) ≤ 2 := by
    apply polynomial_component_span_le_two_of_fraction_presentation (imageRelationNormal H I.equation)
      c (c * t) (fun i => (v i).coeff 0) (fun i => (v i).coeff 1)
    intro i
    change rationalImageNormal H I.equation i = _
    rw [hrep i, heval i]
    ring
  exact dependent_of_normal_component_span_le_two H (imageRelationNormal H I.equation) hd hH
    I.normal_ne_zero (I.left_kernel H) hspan

end DimensionFourDependence
