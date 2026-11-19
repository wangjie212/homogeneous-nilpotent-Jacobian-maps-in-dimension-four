import DimensionFourDependence.PolynomialProjectiveHilbertGrowth
import DimensionFourDependence.CharacteristicPolynomialDegree
import DimensionFourDependence.NonlinearGaussCharacteristic
import DimensionFourDependence.FiberHilbertDegree

/-! # The actual nonplanar characteristic image has projective degree at least three -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]

/-- A lower bound cn+1 for every Hilbert-function value bounds the
positive eventual Hilbert degree from below by c. -/
theorem curve_hilbert_degree_lower_bound_of_linear_growth
    {σ : Type*} (J : Ideal (MvPolynomial σ K)) (c : ℕ)
    (hlower : ∀ n, c * n + 1 ≤ projectiveHilbertFunction J n)
    {D : ℕ} (hD : HasCurveHilbertDegree J D) : c ≤ D := by
  obtain ⟨_hpos, b, N, hN⟩ := hD
  by_contra hn
  have hDc : (D : ℤ) + 1 ≤ c := by exact_mod_cast (show D + 1 ≤ c by omega)
  let n := N + b.natAbs + 1
  have hlow : ((c * n + 1 : ℕ) : ℤ) ≤ (projectiveHilbertFunction J n : ℤ) :=
    Int.ofNat_le.mpr (hlower n)
  push_cast at hlow
  rw [hN n (by dsimp only [n]; omega)] at hlow
  have hn0 : (0 : ℤ) ≤ n := by positivity
  have hmul := mul_le_mul_of_nonneg_right hDc hn0
  have hb : b ≤ (b.natAbs : ℤ) := Int.le_natAbs
  have hnb : (b.natAbs : ℤ) + 1 ≤ n := by
    dsimp only [n]
    push_cast
    omega
  nlinarith

/-- Nonplanarity of a rational vector forces genuine projective
Hilbert growth of slope at least three, independently of the degrees
or multiplicities of a chosen parameterization. -/
theorem nonplanar_rational_curve_projective_hilbert_lower_bound
    (b : Fin 4 → RatFunc K) (hb : b ≠ 0)
    (hplane : ∀ c : Fin 4 → K,
      (fun i => algebraMap K (RatFunc K) (c i)) ⬝ᵥ b = 0 → c = 0) (n : ℕ) :
    3 * n + 1 ≤ projectiveHilbertFunction (projectiveFieldPointIdeal (E := K) b).toIdeal n := by
  obtain ⟨p, _hp, hLI, _hprimitive, ⟨s, hs, hrep⟩, _hparamDegree⟩ :=
    nonplanar_rational_vector_primitive_polynomial_degree_bound b hb hplane
  have he : b = fun i => s * algebraMap (Polynomial K) (RatFunc K) (p i) := funext hrep
  rw [he, projectiveFieldPointIdeal_scale _ s hs]
  exact independent_four_polynomial_coordinates_hilbert_lower_bound p hLI n

/-- Every positive Hilbert degree of the rational characteristic
image is at least three. This is an image-degree bound. -/
theorem nonplanar_rational_curve_projective_degree_at_least_three
    (b : Fin 4 → RatFunc K) (hb : b ≠ 0)
    (hplane : ∀ c : Fin 4 → K,
      (fun i => algebraMap K (RatFunc K) (c i)) ⬝ᵥ b = 0 → c = 0)
    {D : ℕ} (hD : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := K) b).toIdeal D) :
    3 ≤ D :=
  curve_hilbert_degree_lower_bound_of_linear_growth _ 3
    (nonplanar_rational_curve_projective_hilbert_lower_bound b hb hplane) hD

/-- A nonplanar rational image cannot have a positive curve degree
at most two, as needed for the characteristic-curve contradiction. -/
theorem nonplanar_rational_curve_has_no_positive_degree_at_most_two
    (b : Fin 4 → RatFunc K) (hb : b ≠ 0)
    (hplane : ∀ c : Fin 4 → K,
      (fun i => algebraMap K (RatFunc K) (c i)) ⬝ᵥ b = 0 → c = 0) :
    ¬∃ D : ℕ, D ≤ 2 ∧ HasCurveHilbertDegree (projectiveFieldPointIdeal (E := K) b).toIdeal D := by
  rintro ⟨D, hD2, hD⟩
  have := nonplanar_rational_curve_projective_degree_at_least_three b hb hplane hD
  omega

universe u

/-- Containment in a projective curve of degree at most two is
already impossible; equality of the two curve ideals is not required. -/
theorem nonplanar_rational_curve_not_contained_in_degree_two_curve
    (b : Fin 4 → RatFunc K) (hb : b ≠ 0)
    (hplane : ∀ c : Fin 4 → K,
      (fun i => algebraMap K (RatFunc K) (c i)) ⬝ᵥ b = 0 → c = 0)
    (J : Ideal (MvPolynomial (Fin 4) K))
    {D : ℕ} (hD2 : D ≤ 2) (hD : HasCurveHilbertDegree J D)
    (hcontain : J ≤ (projectiveFieldPointIdeal (E := K) b).toIdeal) : False := by
  have hlow (n : ℕ) : 3 * n + 1 ≤ projectiveHilbertFunction J n :=
    (nonplanar_rational_curve_projective_hilbert_lower_bound b hb hplane n).trans
      (projectiveHilbertFunction_antitone hcontain n)
  have := curve_hilbert_degree_lower_bound_of_linear_growth J 3 hlow hD
  omega

variable {K' : Type u} [Field K'] [CharZero K']

/-- The actual original map and tangent-ruling identity construct
the characteristic image's lower Hilbert bound in all original coordinates. -/
theorem actual_characteristic_tangent_projective_hilbert_lower_bound
    (H : Fin 4 → MvPolynomial (Fin 4) K') {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (e : RatFunc K' ≃ₐ[K'] projectiveRatioField (K := K')
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (b : Fin 4 → RatFunc K') (hb : b ≠ 0)
    (hspan : normalRulingSubspace (rationalParameterDerivative K') (gaussParameterNormal H I e) =
      Submodule.span (RatFunc K') (Set.range ![b, fun i => rationalParameterDerivative K' (b i)]))
    (n : ℕ) :
    3 * n + 1 ≤ projectiveHilbertFunction (projectiveFieldPointIdeal (E := K') b).toIdeal n :=
  nonplanar_rational_curve_projective_hilbert_lower_bound b hb
    (actual_characteristic_tangent_has_no_constant_hyperplane H hd hH hind I e b hspan) n

/-- The actual moving characteristic has image degree at least three
whenever that degree is represented by its positive Hilbert polynomial. -/
theorem actual_characteristic_tangent_projective_degree_at_least_three
    (H : Fin 4 → MvPolynomial (Fin 4) K') {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (e : RatFunc K' ≃ₐ[K'] projectiveRatioField (K := K')
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (b : Fin 4 → RatFunc K') (hb : b ≠ 0)
    (hspan : normalRulingSubspace (rationalParameterDerivative K') (gaussParameterNormal H I e) =
      Submodule.span (RatFunc K') (Set.range ![b, fun i => rationalParameterDerivative K' (b i)]))
    {D : ℕ} (hD : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := K') b).toIdeal D) :
    3 ≤ D :=
  curve_hilbert_degree_lower_bound_of_linear_growth _ 3
    (actual_characteristic_tangent_projective_hilbert_lower_bound H hd hH hind I e b hb hspan) hD

/-- An actual nonlinear geometric component of the original map
constructs the moving characteristic, its tangent ruling, every Hilbert
lower bound, and the projective image-degree lower bound together. -/
theorem nonlinear_geometric_component_constructs_characteristic_image_degree_lower_bound
    [IsAlgClosed K']
    (H : Fin 4 → MvPolynomial (Fin 4) K') {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K' E]
    [IsScalarTower K' (polynomialOutputField H) E] [IsAlgClosed E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K') (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    ∃ e : RatFunc K' ≃ₐ[K'] projectiveRatioField (K := K')
      (rationalImageNormal H I.equation) (imageNormalPivot H I),
      let w := gaussParameterNormal H I e
      LinearIndependent (RatFunc K') (normalCharacteristicMatrix (rationalParameterDerivative K') w).row ∧
      ∃ b : Fin 4 → RatFunc K', b ≠ 0 ∧
        b ∈ normalCharacteristicSubspace (rationalParameterDerivative K') w ∧
        LinearIndependent (RatFunc K') ![b, fun i => rationalParameterDerivative K' (b i)] ∧
        normalRulingSubspace (rationalParameterDerivative K') w =
          Submodule.span (RatFunc K') (Set.range ![b, fun i => rationalParameterDerivative K' (b i)]) ∧
        (∀ n : ℕ, 3 * n + 1 ≤ projectiveHilbertFunction
          (projectiveFieldPointIdeal (E := K') b).toIdeal n) ∧
        (∀ D : ℕ, HasCurveHilbertDegree (projectiveFieldPointIdeal (E := K') b).toIdeal D → 3 ≤ D) := by
  obtain ⟨e, hLI, b, hb, hbC, hpair, hspan, hplane, _hNormal, _hspanNormal⟩ :=
    nonlinear_geometric_component_constructs_moving_gauss_characteristic
      H hd hH hN hrank hind I hGauss E P hP hline
  exact ⟨e, hLI, b, hb, hbC, hpair, hspan,
    nonplanar_rational_curve_projective_hilbert_lower_bound b hb hplane,
    fun _ hD => nonplanar_rational_curve_projective_degree_at_least_three b hb hplane hD⟩

end DimensionFourDependence
