import DimensionFourDependence.GeometricAlgebraicSourceEmbedding
import DimensionFourDependence.AlgebraicSourceDerivationChain

/-! # The actual geometric component constructs the original coordinate partials and chain rule -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (s : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s 3)))
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "G₀" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)
local notation "z₀" => primeQuotientCoordinate P
local notation "C₀" => closedGaussParameterField H I

include hY hh hN hrank hP

/-- The actual component constructs its compatible closed Gauss and
source realization, all original coordinate partials, every original
rational derivative, commutation, the chain rule for every actual fiber
derivation and nilpotence of the actual polynomial derivative matrix. -/
theorem geometric_component_constructs_original_partials_and_nilpotent_chain_rule :
    ∃ f : S₀ →ₐ[K] G₀, (∀ i : Fin 4, f (rationalCoordinate (K := K) i) = z₀ i) ∧
      ∃ g : C₀ →ₐ[K] E, (∀ c : C₀, algebraMap E G₀ (g c) = f (c : S₀)) ∧
        letI : Algebra S₀ G₀ := f.toRingHom.toAlgebra
        letI : SMul K S₀ := (inferInstance : Algebra K S₀).toSMul
        letI : SMul S₀ G₀ := (inferInstance : Algebra S₀ G₀).toSMul
        letI : SMul K G₀ := (inferInstance : Algebra K G₀).toSMul
        letI : Module K G₀ := (inferInstance : Algebra K G₀).toModule
        letI : IsScalarTower K S₀ G₀ := IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
        Algebra.IsAlgebraic S₀ G₀ ∧ ∃ D : Fin 4 → Derivation K G₀ G₀,
          (∀ i j, D i (z₀ j) = if j = i then 1 else 0) ∧
          (∀ i (r : S₀), D i (f r) = f (rationalPartial (K := K) i r)) ∧
          (∀ i j (r : G₀), D i (D j r) = D j (D i r)) ∧
          (∀ (Δ : Derivation K G₀ G₀) (r : G₀), Δ r = ∑ i : Fin 4, Δ (z₀ i) * D i r) ∧
          IsNilpotent (Matrix.of (fun i j : Fin 4 => D j (aeval z₀ (H i)))) := by
  obtain ⟨f, hf, g, hg, halg⟩ :=
    geometric_component_constructs_algebraic_source_and_closed_gauss_embedding H I s hY h hh hrank E P hP
  refine ⟨f, hf, g, hg, ?_⟩
  let : Algebra S₀ G₀ := f.toRingHom.toAlgebra
  let : SMul K S₀ := (inferInstance : Algebra K S₀).toSMul
  let : SMul S₀ G₀ := (inferInstance : Algebra S₀ G₀).toSMul
  let : SMul K G₀ := (inferInstance : Algebra K G₀).toSMul
  let : Module K G₀ := (inferInstance : Algebra K G₀).toModule
  let : IsScalarTower K S₀ G₀ := IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
  let : Algebra.IsAlgebraic S₀ G₀ := halg
  have hmap (r : S₀) : algebraMap S₀ G₀ r = f r := rfl
  refine ⟨halg, fun i => algebraicPartial (K := K) (n := 4) G₀ i, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [← hf j]
    exact algebraicPartial_coordinate G₀ i j
  · intro i r
    exact algebraicPartial_extends (K := K) (n := 4) G₀ i r
  · exact algebraicPartials_commute (K := K) (n := 4) G₀
  · intro Δ r
    have hc := algebraic_source_derivation_coordinate_chain_rule Δ r
    simpa only [hmap, hf] using hc
  · have heval (Q : MvPolynomial (Fin 4) K) :
        algebraMap S₀ G₀ (algebraMap (MvPolynomial (Fin 4) K) S₀ Q) = aeval z₀ Q := by
      have he := comp_aeval_apply (rationalCoordinate (K := K) (n := 4)) f Q
      rw [rationalCoordinate_aeval] at he
      rw [hmap]
      simpa only [hf] using he
    simpa only [heval] using algebraic_original_source_partials_jacobian_nilpotent (F := G₀) H hN

end DimensionFourDependence
