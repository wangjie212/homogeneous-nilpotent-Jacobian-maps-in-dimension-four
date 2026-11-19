import DimensionFourDependence.GeometricAlgebraicSourceEmbedding
import DimensionFourDependence.GeometricParameterDirectionAlgebraicity
import DimensionFourDependence.NormalizedClosedConeQuadraticCoefficient
import DimensionFourDependence.RealizedConeMovingNormal
import DimensionFourDependence.RealizedConeNormalIncidence
import DimensionFourDependence.GenericFiberOutput
import DimensionFourDependence.ChangedGaussVertexDifferential

/-! # The actual original geometric cone component constructs its normalized quadratic coefficient

The original pencil constructs parameter algebraicity of the actual
projected direction ratios. The original Jacobian excludes the
proportional direction. All data use one compatible actual source and
closed Gauss realization, and yield the nonzero numerator kappa/R.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

set_option quotPrecheck false
set_option maxHeartbeats 8000000
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

/-- The original vertex-dependent pencil and actual nonlinear
geometric component construct a compatible realization in which every
full cone presentation has normalized quadratic coefficient kappa/R.
No fiber-direction algebraicity or independence, normal jets, tangent
decomposition, directrix derivative or numerator is supplied. -/
theorem geometric_original_cone_constructs_normalized_quadratic_numerator
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
                  (∑ i : Fin 3, algebraMap E G₀ (g (e (closedGaussParameterNormal H I e i.castSucc))) * z₀ i.castSucc)) →
              C / (A j) ^ 2 ≠ 0 ∧ ∃ κ : E, κ ≠ 0 ∧ IsAlgebraic g.fieldRange κ ∧ C / (A j) ^ 2 = κ / R := by
  obtain ⟨f, hf, g, hg, halg⟩ :=
    geometric_component_constructs_algebraic_source_and_closed_gauss_embedding H I s hY h hh hrank E P hP
  refine ⟨f, hf, g, hg, ?_⟩
  intro t ht x A w B C hC hx hw j hj R hR V hV0 a b hb0 hV ha hb hfirst hlast
  let : Algebra S₀ G₀ := f.toRingHom.toAlgebra
  let : SMul K S₀ := (inferInstance : Algebra K S₀).toSMul
  let : SMul S₀ G₀ := (inferInstance : Algebra S₀ G₀).toSMul
  let : SMul K G₀ := (inferInstance : Algebra K G₀).toSMul
  let : Module K G₀ := (inferInstance : Algebra K G₀).toModule
  let : IsScalarTower K S₀ G₀ := IsScalarTower.of_algebraMap_eq (fun c => (f.commutes c).symm)
  let : Algebra.IsAlgebraic S₀ G₀ := halg
  let : CharZero G₀ := charZero_of_injective_algebraMap (algebraMap K G₀).injective
  have hmap (a : S₀) : algebraMap S₀ G₀ a = f a := rfl
  have hcoords (i : Fin 4) : algebraMap S₀ G₀ (rationalCoordinate (K := K) i) = z₀ i := by rw [hmap, hf]
  have hcomp (c : C₀) : algebraMap E G₀ (g c) = algebraMap S₀ G₀ (c : S₀) := by rw [hmap]; exact hg c
  have heval (Q : MvPolynomial (Fin 4) K) :
      algebraMap S₀ G₀ (algebraMap (MvPolynomial (Fin 4) K) S₀ Q) = aeval z₀ Q := by
    rw [hmap]
    have he := comp_aeval_apply (rationalCoordinate (K := K) (n := 4)) f Q
    rw [rationalCoordinate_aeval] at he
    simpa only [hf] using he
  have hout (i : Fin 4) : aeval z₀ (H i) = algebraMap E G₀ (genericOutputValue H E i) := by
    simpa only [aeval_map_coefficients] using geometric_component_generic_output_evaluation H E P hP i
  obtain ⟨ν, k, hk, hdim, _hνvalue, hν⟩ :=
    compatible_closed_gauss_realization_constructs_ternary_moving_normal H I hGauss hvertex e f g hg
  have hinc := realized_fixed_vertex_normal_incident_projected_fiber_direction H hN hrank I hvertex
    f z₀ hf (genericOutputValue H E) hout (fun i => (ν i : E)) hν t ht x A hx
  let : IsScalarTower K g.fieldRange E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hrhom : r.IsHomogeneous m := by rcases hr with rfl | rfl <;> assumption
  obtain ⟨hA, _hfinite, _v, _hvj, _hv⟩ :=
    geometric_parameter_vertex_direction_constructs_finite_ruling_representative H I s hY h hh e hrank E P hP
      hpara hnotline p q hp hq hrel hparameter r hr hrhom hrvertex t ht x A w B C hC hx hw
      g.fieldRange ν k hk hdim hinc j hj
  have hvertexp : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3) := by
    rcases hr with rfl | rfl
    · exact Or.inl hrvertex
    · exact Or.inr hrvertex
  have hsourcevertex := actual_closed_gauss_changed_parameter_vertex_partial_ne_zero H I e e
    p q hp hq hrel hpH hqH hparameter hvertexp
  let p₀ := (IsScalarTower.toAlgHom K S₀ G₀).comp (closedGaussParameterSourceHom H I e)
  have hnormal (i : Fin 3) : p₀ (closedGaussParameterNormal H I e i.castSucc) =
      algebraMap E G₀ (g (e (closedGaussParameterNormal H I e i.castSucc))) :=
    (hcomp (e (closedGaussParameterNormal H I e i.castSucc))).symm
  have hL : (fun i : Fin 3 => p₀ (closedGaussParameterNormal H I e i.castSucc)) ⬝ᵥ
      (fun i : Fin 3 => algebraMap S₀ G₀ (rationalCoordinate (K := K) i.castSucc)) =
        ∑ i : Fin 3, algebraMap E G₀ (g (e (closedGaussParameterNormal H I e i.castSucc))) * z₀ i.castSucc := by
    simp only [dotProduct, hnormal, hcoords]
  apply actual_closed_cone_projective_direction_constructs_normalized_quadratic_numerator H I e g hcomp
    hd hH hN hrank hind hGauss hvertex hsourcevertex t ht x A V w B C R
    (genericOutputValue H E (Fin.last 3)) a b hC hV0 j hj
  · intro i
    change algebraMap S₀ G₀ (rationalCoordinate (K := K) i.castSucc) = _
    rw [hcoords]; exact hx i
  · change algebraMap S₀ G₀ (rationalCoordinate (K := K) (Fin.last 3)) = _
    rw [hcoords]; exact hw
  · rw [heval]; exact hout _
  · exact hR
  · exact hb0
  · intro i; rw [heval]; exact hfirst i
  · rw [heval, hL]; exact hlast
  · exact hV
  · exact hA
  · exact ha
  · exact hb

end DimensionFourDependence
