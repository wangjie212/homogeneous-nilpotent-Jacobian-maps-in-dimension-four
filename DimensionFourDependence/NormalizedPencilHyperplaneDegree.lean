import DimensionFourDependence.HomogeneousPrincipalHilbert
import DimensionFourDependence.ExtendedGaussPencilScheme
import DimensionFourDependence.ProperBirationalDivisorLift

/-! # The hyperplane-square degree of the normalized pencil -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
set_option maxHeartbeats 3800000
set_option synthInstance.maxHeartbeats 140000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The degree of a projective surface is twice the quadratic
coefficient of its Hilbert polynomial, expressed by the eventual
second finite difference of its Hilbert function. -/
def HasSurfaceHilbertDegree {k : Type u} [Field k]
    (J : Ideal (MvPolynomial (Fin 4) k)) (D : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, projectiveHilbertFunction J (n + 2) + projectiveHilbertFunction J n =
    2 * projectiveHilbertFunction J (n + 1) + D

private theorem four_variable_homogeneous_second_difference {k : Type u} [Field k] (n : ℕ) :
    Module.finrank k (homogeneousSubmodule (Fin 4) k (n + 2)) +
      Module.finrank k (homogeneousSubmodule (Fin 4) k n) =
    2 * Module.finrank k (homogeneousSubmodule (Fin 4) k (n + 1)) + (n + 3) := by
  simp only [homogeneousPiece_finrank, Nat.card_fin]
  have h₀ : (4 + n - 1) = n + 3 := by omega
  have h₁ : (4 + (n + 1) - 1) = (n + 3) + 1 := by omega
  have h₂ : (4 + (n + 2) - 1) = ((n + 3) + 1) + 1 := by omega
  rw [h₂, h₁, h₀, ← Nat.choose_symm (by omega : n + 2 ≤ n + 3 + 1 + 1),
    ← Nat.choose_symm (by omega : n + 1 ≤ n + 3 + 1),
    ← Nat.choose_symm (by omega : n ≤ n + 3)]
  rw [show n + 3 + 1 + 1 - (n + 2) = 3 by omega,
    show n + 3 + 1 - (n + 1) = 3 by omega, show n + 3 - n = 3 by omega,
    Nat.choose_succ_succ' ((n + 3) + 1) 2,
    Nat.choose_succ_succ' (n + 3) 2,
    Nat.choose_succ_succ' (n + 3) 1, Nat.choose_one_right]
  simp only [show (1 + 1 : ℕ) = 2 by decide, show (2 + 1 : ℕ) = 3 by decide]
  omega

/-- A nonzero homogeneous equation in four variables has projective
surface Hilbert degree equal to the degree of the equation. -/
theorem homogeneous_hypersurface_surface_hilbert_degree {k : Type u} [Field k]
    (P : MvPolynomial (Fin 4) k) {D : ℕ} (hp : P.IsHomogeneous D) (hp₀ : P ≠ 0) :
    HasSurfaceHilbertDegree (Ideal.span {P}) D := by
  refine ⟨D, fun n hn => ?_⟩
  let m := n - D
  have hm : m + D = n := Nat.sub_add_cancel hn
  have h₀ := homogeneous_principal_hilbert_identity P hp hp₀ m
  have h₁ := homogeneous_principal_hilbert_identity P hp hp₀ (m + 1)
  have h₂ := homogeneous_principal_hilbert_identity P hp hp₀ (m + 2)
  rw [hm] at h₀
  rw [show m + 1 + D = n + 1 by omega] at h₁
  rw [show m + 2 + D = n + 2 by omega] at h₂
  have h₃ := four_variable_homogeneous_second_difference (k := k) m
  have h₄ := four_variable_homogeneous_second_difference (k := k) n
  omega

section Normalization

variable (X : Scheme.{u}) [IsIntegral X]
local notation "Y" => integralSchemeNormalization X
local notation "p" => integralSchemeNormalizationMap X
local notation "j" => integralSchemeNormalizationGenericPoint X

local instance : IsIntegral Y := integralSchemeNormalization_isIntegral X

theorem integralSchemeNormalizationMap_isDominant : IsDominant p := by
  have : IsDominant (j ≫ p) := integralSchemeNormalization_factorization X ▸
    integralSchemeGenericPointMorphism_isDominant X
  exact IsDominant.of_comp j p

local instance : IsDominant p := integralSchemeNormalizationMap_isDominant X

/-- The actual normalization induces an isomorphism on function fields. -/
theorem integralSchemeNormalizationMap_functionField_surjective :
    Function.Surjective (dominantFunctionFieldHom p) := by
  let x := IsLocalRing.closedPoint X.functionField
  let : IsDominant j := by unfold integralSchemeNormalizationGenericPoint; infer_instance
  have hη : j x = genericPoint Y := by
    have hx : x = genericPoint (Spec X.functionField) := Subsingleton.elim _ _
    exact congrArg j hx |>.trans (dominant_map_generic_point j)
  have hj : Function.Injective (Scheme.stalkClosedPointTo j).hom := by
    let : IsSimpleRing ((Y).presheaf.stalk (j x)) :=
      hη ▸ inferInstanceAs (IsSimpleRing ((Y).functionField))
    exact (Scheme.stalkClosedPointTo j).hom.injective
  have hiso : IsIso (Scheme.stalkClosedPointTo (j ≫ p)) := by
    rw [integralSchemeNormalization_factorization, integralSchemeGenericPointMorphism,
      Scheme.stalkClosedPointTo_fromSpecStalk]
    infer_instance
  have hp : Function.Surjective ((p).stalkMap (j x)).hom := by
    intro r
    obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.stalkClosedPointTo (j ≫ p))).surjective
      (Scheme.stalkClosedPointTo j r)
    refine ⟨a, hj ?_⟩
    rwa [Scheme.stalkClosedPointTo_comp] at ha
  have hgen : Function.Surjective ((p).stalkMap (genericPoint Y)).hom :=
    (congrArg (fun z : Y => Function.Surjective ((p).stalkMap z).hom) hη).mp hp
  unfold dominantFunctionFieldHom
  exact hgen.comp (ConcreteCategory.bijective_of_isIso
    (X.presheaf.stalkCongr (Inseparable.of_eq
      (dominant_map_generic_point p).symm)).hom).surjective

/-- Pushforward of the normalized surface has coefficient one at
the generic point of its projective image. -/
theorem integralSchemeNormalizationMap_generic_degree :
    letI := (dominantFunctionFieldHom p).toAlgebra
    Module.finrank X.functionField (Y).functionField = 1 := by
  let := (dominantFunctionFieldHom p).toAlgebra
  apply finrank_eq_one (1 : (Y).functionField) one_ne_zero
  intro r
  obtain ⟨a, ha⟩ := integralSchemeNormalizationMap_functionField_surjective X r
  exact ⟨a, by rw [Algebra.smul_def, mul_one]; exact ha⟩

end Normalization

/-- The exact surface Hilbert degree on the original extended pencil
is its homogeneous equation degree. With the normalization's generic
degree one, this computes the hyperplane-square degree by pushforward. -/
theorem extended_closed_gauss_pencil_surface_hilbert_degree
    {K E : Type u} [Field K] [CharZero K] [Field E]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    [Algebra (closedGaussParameterField H I) E]
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) {D : ℕ} (hq : q ≠ 0)
    (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q) :
    HasSurfaceHilbertDegree (extendedClosedGaussPencilIdeal H I E) D := by
  let f := algebraMap (closedGaussParameterField H I) E
  obtain ⟨hn, hh, _⟩ := actual_closed_gauss_pencil_homogeneous_degree H I e p q hq hrel hpH hqH
  change HasSurfaceHilbertDegree (extendCoefficientIdeal E _) D
  rw [actual_closed_gauss_pencil_relation_ideal H I e p q hq hrel ht,
    extendCoefficientIdeal, Ideal.map_span, Set.image_singleton]
  exact homogeneous_hypersurface_surface_hilbert_degree _ (hh.map f)
    ((MvPolynomial.map_injective (σ := Fin 4) f f.injective).ne hn |>.trans_eq (map_zero _))

/-- The normalized pencil has hyperplane-square degree equal to its
equation degree in the projective pushforward formula. This computes
both the generic multiplicity of the pushforward and the Hilbert
degree of its actual projective image. -/
theorem extended_closed_gauss_pencil_hyperplane_square_degree
    {K E : Type u} [Field K] [CharZero K] [Field E]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    [Algebra (closedGaussParameterField H I) E] [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) {D : ℕ} (hq : q ≠ 0)
    (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q) :
    let Z := extendedClosedGaussPencilScheme H I E hH e
    letI : IsIntegral Z := extendedClosedGaussPencilScheme_isIntegral H I E hH e
    let Y := integralSchemeNormalization Z
    letI : IsIntegral Y := integralSchemeNormalization_isIntegral Z
    letI : IsDominant (integralSchemeNormalizationMap Z) := integralSchemeNormalizationMap_isDominant Z
    letI := (dominantFunctionFieldHom (integralSchemeNormalizationMap Z)).toAlgebra
    ∃ D₀, HasSurfaceHilbertDegree (extendedClosedGaussPencilIdeal H I E) D₀ ∧
      Module.finrank Z.functionField Y.functionField * D₀ = D := by
  dsimp only
  refine ⟨D, extended_closed_gauss_pencil_surface_hilbert_degree H I e p q hq hrel hpH hqH ht, ?_⟩
  rw [integralSchemeNormalizationMap_generic_degree, one_mul]

end DimensionFourDependence
