import DimensionFourDependence.NonlinearGeometricDependence
import DimensionFourDependence.OriginalLineFiberKernelAcceleration
import DimensionFourDependence.ZeroAccelerationPolynomialTranslation

/-! # The original independent rank-three map constructs its own quasi-translation -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- Actual components over algebraic generic constants exist: the
extended original fiber prime is proper by integral coefficient extension. -/
theorem exists_original_geometric_generic_component
    (H : Fin 4 → R₀) (E : Type u) [Field E]
    [Algebra (polynomialOutputField H) E] [Algebra.IsAlgebraic (polynomialOutputField H) E] :
    ∃ P : Ideal (MvPolynomial (Fin 4) E), P.IsPrime ∧
      P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
        (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes := by
  let M := polynomialOutputField H
  let I := fiberVanishingIdeal (L := M) (rationalCoordinate (K := K) (n := 4))
  let f : MvPolynomial (Fin 4) M →+* MvPolynomial (Fin 4) E :=
    MvPolynomial.map (algebraMap M E)
  have hint : f.IsIntegral := by
    change (MvPolynomial.map (algebraMap M E)).IsIntegral
    rw [← MvPolynomial.algebraMap_def]
    exact algebraMap_isIntegral_iff.mpr inferInstance
  have hproper : extendCoefficientIdeal E I ≠ ⊤ := by
    change I.map f ≠ ⊤
    intro htop
    apply Ideal.IsPrime.ne_top (inferInstance : I.IsPrime)
    exact (Ideal.map_eq_top_iff f
      (MvPolynomial.map_injective (algebraMap M E) (algebraMap M E).injective) hint).mp htop
  obtain ⟨P, hP⟩ := (extendCoefficientIdeal E I).nonempty_minimalPrimes hproper
  exact ⟨P, hP.isPrime, hP⟩

variable [CharZero K] [IsAlgClosed K]

/-- With independence assumed for contradiction, the original map
constructs a primitive homogeneous zero-acceleration direction.
No geometric component or line hypothesis is supplied: an actual
component is chosen and the checked nonlinear branch forces it to be a line. -/
theorem original_independent_rank_three_map_constructs_zero_acceleration_kernel_over_generic_constants
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H)
    (E : Type u) [Field E] [IsAlgClosed E]
    [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E] :
    ∃ (u : Fin 4 → R₀) (e : ℕ), IsPrimRightKernel (jac H) u e ∧ jac u *ᵥ u = 0 := by
  obtain ⟨P, hprime, hP⟩ := exists_original_geometric_generic_component H E
  let : P.IsPrime := hprime
  have hline : LiesInAffineLine (E := E) (primeQuotientCoordinate P) := by
    by_contra hn
    exact hind (nonlinear_geometric_generic_component_forces_componentsDependent
      H hd hH hN hrank E P hP hn)
  exact original_homogeneous_affine_line_component_constructs_zero_acceleration_kernel
    H hH hrank E P hP hline

/-- The original source constructs its own geometric constants as
well; the conclusion lies entirely over the original closed constants. -/
theorem original_independent_rank_three_map_constructs_zero_acceleration_kernel
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) :
    ∃ (u : Fin 4 → R₀) (e : ℕ), IsPrimRightKernel (jac H) u e ∧ jac u *ᵥ u = 0 := by
  let M := polynomialOutputField H
  let E := AlgebraicClosure M
  exact original_independent_rank_three_map_constructs_zero_acceleration_kernel_over_generic_constants
    H hd hH hN hrank hind E

/-- The original independent rank-three map constructs a nonzero
primitive homogeneous direction, all parameter translation invariants,
and the actual inverse polynomial automorphisms required before the
remaining homogeneous quasi-translation classification. -/
theorem original_independent_rank_three_map_constructs_polynomial_quasi_translation
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) :
    ∃ (u : Fin 4 → R₀) (e : ℕ), IsPrimRightKernel (jac H) u e ∧ jac u *ᵥ u = 0 ∧
      (∀ s : K, ∀ i, polynomialDirectionTranslation u s (u i) = u i) ∧
      (∀ s : K, ∀ i, polynomialDirectionTranslation u s (H i) = H i) ∧
      (∀ s : K, ∃ T : R₀ ≃ₐ[K] R₀,
        T.toAlgHom = polynomialDirectionTranslation u s ∧
        T.symm.toAlgHom = polynomialDirectionTranslation u (-s)) := by
  obtain ⟨u, e, hu, hacc⟩ :=
    original_independent_rank_three_map_constructs_zero_acceleration_kernel H hd hH hN hrank hind
  refine ⟨u, e, hu, hacc,
    zero_acceleration_polynomial_translation_preserves_direction u hacc,
    zero_acceleration_polynomial_translation_preserves_kernel_map u hacc H hu.ker, ?_⟩
  intro s
  exact ⟨zeroAccelerationPolynomialTranslationEquiv u hacc s, rfl, rfl⟩

end DimensionFourDependence
