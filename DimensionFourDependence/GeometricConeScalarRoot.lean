import DimensionFourDependence.ClosedConeScalarDirection
import DimensionFourDependence.GeometricClosedGaussEmbedding
import DimensionFourDependence.GenericFiberOutput

/-! # The first three cone coordinates and their root on the actual fiber

The constructed closed-cover directrix is realized through the compatible
source and closed-field embeddings of the actual geometric component.
Its normalized output is nonzero. Algebraic closedness supplies its
degree-d root and gives the first three scalar formulas of (4.7).
The last output formula and the parabolic vertex coefficient are separate.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

universe u

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (s : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s 3)))
    (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "G₀" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)
local notation "z₀" => primeQuotientCoordinate P

include hd hH hind hGauss hvertex hY hh hrank hP

/-- The original fixed-vertex Gauss data construct the first three
scalar cone-coordinate formulas on every actual geometric component.
The same constructed embeddings realize all original coordinates and
all closed-cover coefficients; neither a scalar presentation nor a
nonzero output value nor a chosen root is supplied. -/
theorem geometric_fixed_vertex_cone_constructs_scalar_root_presentation
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) :
    ∃ f : S₀ →ₐ[K] G₀, (∀ i : Fin 4, f (rationalCoordinate (K := K) i) = z₀ i) ∧
      ∃ g : closedGaussParameterField H I →ₐ[K] E,
        (∀ c : closedGaussParameterField H I, algebraMap E G₀ (g c) = f (c : S₀)) ∧
        ∃ (V : Fin 3 → RatFunc K) (j : Fin 3) (R : E),
          V j = 1 ∧ H j.castSucc ≠ 0 ∧ LinearIndependent K V ∧
          LinearIndependent K (fun i => g (e (V i))) ∧ R ≠ 0 ∧
          R ^ d = genericOutputValue H E j.castSucc ∧
          (∀ i : Fin 3, genericOutputValue H E i.castSucc = g (e (V i)) * R ^ d) ∧
          (∀ i : Fin 3, aeval z₀ (H i.castSucc) =
            algebraMap E G₀ (g (e (V i))) * (algebraMap E G₀ R) ^ d) ∧
          (fun i : Fin 3 => closedGaussParameterNormal H I e i.castSucc) ⬝ᵥ V = 0 ∧
          (fun i : Fin 3 => rationalParameterDerivative K
            (closedGaussParameterNormal H I e i.castSucc)) ⬝ᵥ V = 0 ∧
          (fun i : Fin 3 => closedGaussParameterNormal H I e i.castSucc) ⬝ᵥ
            (fun i => rationalParameterDerivative K (V i)) = 0 := by
  classical
  obtain ⟨V, j, hVj, hHj, hLI, hvalues, hnormal, hderivative, htangent⟩ :=
    closed_fixed_vertex_cone_constructs_rational_scalar_direction H hd hH hind I hGauss hvertex e
  obtain ⟨f, hf, g, hg⟩ :=
    geometric_component_constructs_closed_gauss_field_embedding H I s hY h hh hrank E P hP
  have heval (Q : MvPolynomial (Fin 4) K) :
      f (algebraMap (MvPolynomial (Fin 4) K) S₀ Q) = aeval z₀ Q := by
    have he := comp_aeval_apply (rationalCoordinate (K := K) (n := 4)) f Q
    rw [rationalCoordinate_aeval] at he
    simpa only [hf] using he
  have hout (i : Fin 4) : aeval z₀ (H i) = algebraMap E G₀ (genericOutputValue H E i) := by
    simpa only [aeval_map_coefficients] using geometric_component_generic_output_evaluation H E P hP i
  have hyj : genericOutputValue H E j.castSucc ≠ 0 := by
    intro hz
    apply hHj
    apply IsFractionRing.injective (MvPolynomial (Fin 4) K) S₀
    apply f.injective
    change f (algebraMap (MvPolynomial (Fin 4) K) S₀ (H j.castSucc)) =
      f (algebraMap (MvPolynomial (Fin 4) K) S₀ 0)
    simp only [heval, hout, hz, map_zero]
  obtain ⟨R, hR⟩ := IsAlgClosed.exists_pow_nat_eq (genericOutputValue H E j.castSucc) hd
  have hR0 : R ≠ 0 := by
    intro hz
    rw [hz, zero_pow (Nat.ne_of_gt hd)] at hR
    exact hyj hR.symm
  have hfirst (i : Fin 3) : aeval z₀ (H i.castSucc) =
      algebraMap E G₀ (g (e (V i))) * (algebraMap E G₀ R) ^ d := by
    rw [← heval, hvalues i, map_mul]
    change f ((e (V i) : closedGaussParameterField H I) : S₀) *
      f (algebraMap (MvPolynomial (Fin 4) K) S₀ (H j.castSucc)) = _
    rw [← hg, heval, hout, ← hR, map_pow]
  have hgeneric (i : Fin 3) : genericOutputValue H E i.castSucc = g (e (V i)) * R ^ d := by
    apply (algebraMap E G₀).injective
    rw [← hout, map_mul, map_pow]
    exact hfirst i
  let ψ : RatFunc K →ₐ[K] E := g.comp e.toAlgHom
  have hLI' : LinearIndependent K (fun i => g (e (V i))) :=
    hLI.map' ψ.toLinearMap (LinearMap.ker_eq_bot.mpr ψ.injective)
  exact ⟨f, hf, g, hg, V, j, R, hVj, hHj, hLI, hLI', hR0, hR,
    hgeneric, hfirst, hnormal, hderivative, htangent⟩

end DimensionFourDependence
