import DimensionFourDependence.GeometricFixedConeExclusion
import DimensionFourDependence.GeometricConeQuadraticCoefficient
import DimensionFourDependence.ConeQuadraticRootNormalization
import DimensionFourDependence.ParabolaDirectionNormalization

/-! # The actual constructed quadratic coefficient closes the specified full cone case

The source coordinates determine the compatible closed Gauss realization
uniquely. The quadratic-coefficient construction and final affine-parameter
exclusion therefore use the same actual field. Normalizing the fiber
direction and cone root supplies all data of that exclusion internally.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

set_option quotPrecheck false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (s : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s 3)))
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
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

include hY hh hd hH hN hrank hind hGauss hvertex hP

/-- The original map, vertex-dependent pencil and actual nonlinear
vertex parabola exclude every actual full cone presentation in their
compatible closed Gauss realization. No quadratic numerator, direction
normalization, direction independence, algebraicity, moving normal or
derivative condition is supplied to the exclusion. -/
theorem geometric_original_full_cone_data_impossible_with_constructed_quadratic_coefficient
    (e : RatFunc K ≃ₐ[K] C₀)
    (hpara : LiesInAffineParabola (L := E) z₀) (hnotline : ¬ LiesInAffineLine (E := E) z₀)
    (p q : MvPolynomial (Fin 4) K) (hp : p ≠ 0) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    {m : ℕ} (hpH : p.IsHomogeneous m) (hqH : q.IsHomogeneous m)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (r : MvPolynomial (Fin 4) K) (hr : r = p ∨ r = q) (hrvertex : 0 < r.degreeOf (Fin.last 3)) :
    ∃ f : S₀ →ₐ[K] G₀, (∀ i : Fin 4, f (rationalCoordinate (K := K) i) = z₀ i) ∧
      ∃ g : C₀ →ₐ[K] E, (∀ c : C₀, algebraMap E G₀ (g c) = f (c : S₀)) ∧
        ∀ (t : G₀), Transcendental E t → ∀ (x A : Fin 3 → E) (w B C : E), C ≠ 0 →
          (∀ i : Fin 3, z₀ i.castSucc = algebraMap E G₀ (x i) + algebraMap E G₀ (A i) * t) →
          (z₀ (Fin.last 3) = algebraMap E G₀ w + algebraMap E G₀ B * t + algebraMap E G₀ C * t ^ 2) →
          ∀ (j : Fin 3), A j ≠ 0 → ∀ (R : E), R ≠ 0 → ∀ (V : Fin 3 → E), V ≠ 0 →
            ∀ (a b : E), b ≠ 0 → (∀ i, IsAlgebraic g.fieldRange (V i)) →
              IsAlgebraic g.fieldRange a → IsAlgebraic g.fieldRange b →
              (∀ i : Fin 3, aeval z₀ (H i.castSucc) = algebraMap E G₀ (V i) * (algebraMap E G₀ R) ^ d) →
              (aeval z₀ (H (Fin.last 3)) = algebraMap E G₀ a * (algebraMap E G₀ R) ^ d +
                algebraMap E G₀ b * (algebraMap E G₀ R) ^ (d - 1) *
                  (∑ i : Fin 3, algebraMap E G₀ (g (e (closedGaussParameterNormal H I e i.castSucc))) * z₀ i.castSucc)) → False := by
  obtain ⟨g₀, hcompat₀, hexclude⟩ := geometric_fixed_vertex_cone_data_impossible H hd hH hN hrank E P hP
    hind I s hY h hh e hpara hnotline p q hp hq hrel hpH hqH hparameter r hr hrvertex
  obtain ⟨f, hf, g, hg, hcoefficient⟩ := geometric_original_cone_constructs_normalized_quadratic_numerator
    H I s hY h hh hd hH hN hrank hind hGauss hvertex E P hP e hpara hnotline
    p q hp hq hrel hpH hqH hparameter r hr hrvertex
  have heq : g₀ = g := compatible_geometric_source_realization_unique H I P g₀ g hcompat₀ ⟨f, hf, hg⟩
  rw [heq] at hexclude
  refine ⟨f, hf, g, hg, ?_⟩
  intro t ht x A w B C hC hx hw j hj R hR V hV0 a b hb0 hV ha hb hfirst hlast
  obtain ⟨_hCnorm0, κ, hκ0, hκalg, hCκ⟩ :=
    hcoefficient t ht x A w B C hC hx hw j hj R hR V hV0 a b hb0 hV ha hb hfirst hlast
  obtain ⟨htnew, hAjnew, _hCnew, hxnew, hwnew⟩ :=
    actual_vertex_parabola_normalizes_projected_direction t ht z₀ x A w B C hC j hj hx hw
  let Rnew := R / κ
  let Vnew : Fin 3 → E := fun i => V i * κ ^ d
  let anew := a * κ ^ d
  let bnew := b * κ ^ (d - 1)
  have hRnew : Rnew ≠ 0 := div_ne_zero hR hκ0
  have hCunit : C / (A j) ^ 2 = 1 / Rnew := by
    change C / (A j) ^ 2 = 1 / (R / κ)
    rw [hCκ]
    field_simp [hR, hκ0]
  have halg := cone_root_rescaling_preserves_algebraic_coefficients V a b κ d hV ha hb hκalg
  let Λ := ∑ i : Fin 3, algebraMap E G₀ (g (e (closedGaussParameterNormal H I e i.castSucc))) * z₀ i.castSucc
  have hscale := cone_root_rescaling_normalizes_quadratic_coefficient
    (algebraMap E G₀ R) (algebraMap E G₀ κ) (algebraMap E G₀ (C / (A j) ^ 2))
    (algebraMap E G₀ a) (algebraMap E G₀ b) Λ (fun i => algebraMap E G₀ (V i)) d
    (by simpa only [map_zero] using (algebraMap E G₀).injective.ne hR)
    (by simpa only [map_zero] using (algebraMap E G₀).injective.ne hκ0)
    (by rw [hCκ, map_div₀])
  have hfirstnew (i : Fin 3) : aeval z₀ (H i.castSucc) =
      algebraMap E G₀ (Vnew i) * (algebraMap E G₀ Rnew) ^ d := by
    rw [hfirst]
    dsimp only [Vnew, Rnew]
    simpa only [map_mul, map_pow, map_div₀] using hscale.2.2.1 i
  have hlastnew : aeval z₀ (H (Fin.last 3)) = algebraMap E G₀ anew * (algebraMap E G₀ Rnew) ^ d +
      algebraMap E G₀ bnew * (algebraMap E G₀ Rnew) ^ (d - 1) * Λ := by
    rw [hlast]
    dsimp only [anew, bnew, Rnew]
    simpa only [map_mul, map_pow, map_div₀] using hscale.2.2.2.1
  obtain ⟨ν, k, hk, hdim, hνvalue, hν⟩ :=
    compatible_closed_gauss_realization_constructs_ternary_moving_normal H I hGauss hvertex e f g hg
  have hout (i : Fin 4) : aeval z₀ (H i) = algebraMap E G₀ (genericOutputValue H E i) := by
    simpa only [aeval_map_coefficients] using geometric_component_generic_output_evaluation H E P hP i
  have hincnew := realized_fixed_vertex_normal_incident_projected_fiber_direction H hN hrank I hvertex
    f z₀ hf (genericOutputValue H E) hout (fun i => (ν i : E)) hν
    (algebraMap E G₀ (A j) * t) htnew x (fun i => A i / A j) hxnew
  apply hexclude (algebraMap E G₀ (A j) * t) htnew x (fun i => A i / A j)
    w (B / A j) (C / (A j) ^ 2) hxnew hwnew ν k hk hdim hincnew j hAjnew
    Rnew hRnew (1 : g.fieldRange) one_ne_zero (by simpa using hCunit) Vnew anew bnew
    halg.1 halg.2.1 halg.2.2 hfirstnew
  simpa only [hνvalue] using hlastnew

end DimensionFourDependence
