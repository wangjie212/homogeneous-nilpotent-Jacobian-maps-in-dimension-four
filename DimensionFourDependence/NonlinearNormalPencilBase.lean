import DimensionFourDependence.IndependentNormalPencilBase

/-! # Nonlinear Gauss-curve fibers force their entire source pencil base into H = 0 -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate P))

include hd hH hN hrank hind hGauss hP hline

/-- A nonlinear actual component rules out every constant relation
among the original image-normal coordinates, not only a chosen vertex. -/
theorem nonlinear_geometric_component_original_normal_independent :
    LinearIndependent K (rationalImageNormal H I.equation) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  by_contra hci
  have hc0 : c ≠ 0 := fun hz => hci (congrFun hz i)
  have hnormal : rationalImageNormal H I.equation ⬝ᵥ
      (fun j => algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (c j)) = 0 := by
    simpa only [Algebra.smul_def, dotProduct, mul_comm] using hc
  exact original_common_vertex_map_has_no_nonlinear_geometric_component
    H hd hH hN hrank hind I hGauss c hc0 hnormal E P hP hline

/-- The nonlinear original-map hypotheses construct the independent
normal needed to force every field-valued source pencil-base point into H = 0. -/
theorem nonlinear_geometric_component_pencil_base_outputs_zero
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) q)
    {F : Type*} [Field F] [Algebra K F]
    (ψ : MvPolynomial (Fin 4) K →ₐ[K] F) (hpψ : ψ p = 0) (hqψ : ψ q = 0) :
    ∀ i, ψ (H i) = 0 := by
  exact original_independent_normal_pencil_base_outputs_zero H (by omega) hH I
    (nonlinear_geometric_component_original_normal_independent H hd hH hN hrank hind I hGauss E P hP hline)
    e p q hq hrel hparameter ψ hpψ hqψ

/-- Each original output vanishes on every component of the source
pencil base, with the statement retained in the original radical ideal. -/
theorem nonlinear_geometric_component_pencil_base_radical_contains_outputs
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) q) :
    ∀ i, H i ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).radical := by
  exact original_independent_normal_pencil_base_radical_contains_outputs H (by omega) hH I
    (nonlinear_geometric_component_original_normal_independent H hd hH hN hrank hind I hGauss E P hP hline)
    e p q hq hrel hparameter

end DimensionFourDependence
