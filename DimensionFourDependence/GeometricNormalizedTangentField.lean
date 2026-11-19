import DimensionFourDependence.GeometricBranchTangentProportionality
import DimensionFourDependence.GeometricParameterDirectionAlgebraicity
import DimensionFourDependence.CommonFiniteDirectionTangentField

/-! # The actual normalized direction constructs its finite tangent field

The original pencil constructs the proper direction equation. Incidence
with the specified moving normal makes the normalized actual direction
algebraic over the constructed Gauss image field. That finite coordinate
field and source independence are both constructed. The tangent ratio
then joins the actual directions in one actual finite ruling extension.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

universe u

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "G₀" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)
local notation "z₀" => primeQuotientCoordinate P

include hd hH hN hrank hP

/-- The actual reduced pencil constructs its Gauss field realization
and one finite extension containing the normalized original direction
and its nonzero tangent multiplier. No direction coefficient field,
algebraicity, source independence, curve equation or invariant constant
is supplied. The specified vertex and moving-normal geometry remains. -/
theorem geometric_normalized_vertex_pencil_constructs_common_finite_tangent_field
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (s : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s i.castSucc))))
    (hh : (h : S₀) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hpara : LiesInAffineParabola (L := E) z₀) (hline : ¬ LiesInAffineLine (E := E) z₀)
    (p q : MvPolynomial (Fin 4) K) (hp : p ≠ 0) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    {D : ℕ} (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (r : MvPolynomial (Fin 4) K) (hr : r = p ∨ r = q) (hrvertex : 0 < r.degreeOf (Fin.last 3)) :
    ∃ g : closedGaussParameterField H I →ₐ[K] E, ∃ f : S₀ →ₐ[K] G₀,
      (∀ i : Fin 4, f (rationalCoordinate (K := K) i) = z₀ i) ∧
      (∀ c : closedGaussParameterField H I, algebraMap E G₀ (g c) = f (c : S₀)) ∧
      ∀ (t : G₀), Transcendental E t → ∀ (x A : Fin 3 → E) (w0 B C : E),
      (∀ i : Fin 3, z₀ i.castSucc = algebraMap E G₀ (x i) + algebraMap E G₀ (A i) * t) →
      (z₀ (Fin.last 3) = algebraMap E G₀ w0 + algebraMap E G₀ B * t + algebraMap E G₀ C * t ^ 2) →
      ∀ (nu : Fin 3 → g.fieldRange) (k : Fin 3), nu k ≠ 0 →
      Algebra.trdeg K (projectiveRatioField (K := K) nu k) ≠ 0 →
      (∑ i : Fin 3, (nu i : E) * A i) = 0 → ∀ (j : Fin 3), A j = 1 →
      ∀ (R : E), R ≠ 0 → ∀ (κ : g.fieldRange), κ ≠ 0 → C = (κ : E) / R →
      ∃ (Φ : MvPolynomial (Fin 3) K) (m : ℕ),
        Φ ≠ 0 ∧ Φ.IsHomogeneous m ∧ 0 < m ∧ Irreducible Φ ∧
        (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ} ∧
        let T := ∑ i : Fin 3, aeval A (pderiv i Φ) * x i
        IsAlgebraic g.fieldRange (R / T) ∧
          ∃ L : IntermediateField g.fieldRange E, Module.Finite g.fieldRange L ∧
            (∀ i, A i ∈ L) ∧ ∃ u : L, u ≠ 0 ∧ R = (u : E) * T := by
  obtain ⟨g, f, hf, hg, hbranch⟩ := geometric_vertex_pencil_constructs_tangent_proportionality_on_algebraic_branches
    H hd hH hN hrank E P hP hind I s hY h hh e hpara hline p q hp hq hrel hpH hqH hparameter r hr hrvertex
  refine ⟨g, f, hf, hg, ?_⟩
  intro t ht x A w0 B C hx hw nu k hk hdim hinc j hj R hR κ hκ hC
  let J := g.fieldRange
  have hrhom : r.IsHomogeneous D := by rcases hr with rfl | rfl <;> assumption
  have hC0 : C ≠ 0 := by
    rw [hC]
    exact div_ne_zero (by exact_mod_cast hκ) hR
  have hj0 : A j ≠ 0 := by rw [hj]; exact one_ne_zero
  obtain ⟨halg, hfinite, v, _hvj, hv⟩ :=
    geometric_parameter_vertex_direction_constructs_finite_ruling_representative
      H I s hY h hh e hrank E P hP hpara hline p q hp hq hrel hparameter r hr hrhom hrvertex
      t ht x A w0 B C hC0 hx hw J nu k hk hdim hinc j hj0
  let F := IntermediateField.adjoin J (Set.range (fun i => A i / A j))
  let : Module.Finite J F := hfinite
  let : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (by intro a; rfl)
  let : IsScalarTower J F E := IsScalarTower.of_algebraMap_eq (by intro a; rfl)
  have hvE : (fun i => algebraMap F E (v i)) = A := by
    funext i
    rw [IntermediateField.algebraMap_apply]
    have he : A i = 1 * (v i : E) :=
      (hv i).trans (congrArg (fun a : E => a * (v i : E)) hj)
    simpa only [one_mul] using he.symm
  have hxv (i : Fin 3) : z₀ i.castSucc = algebraMap E G₀ (x i) + algebraMap F G₀ (v i) * t := by
    have hmap : algebraMap F G₀ (v i) = algebraMap E G₀ (A i) := by
      change algebraMap E G₀ (algebraMap F E (v i)) = algebraMap E G₀ (A i)
      rw [congrFun hvE i]
    rw [hmap]
    exact hx i
  let κF : F := algebraMap J F κ
  have hκF : κF ≠ 0 := by
    simpa only [map_zero] using (algebraMap J F).injective.ne hκ
  have hCF : C = algebraMap F E κF / R := hC
  obtain ⟨Φ, m, hΦ0, hΦ, hm, hirr, hIF, halgF, _hfiniteT, u, _hu, huR⟩ :=
    hbranch F inferInstance t ht x v w0 B C hxv hw R hR κF hκF hCF
  rw [hvE] at halgF
  let T : E := ∑ i : Fin 3, aeval A (pderiv i Φ) * x i
  have hTvalue : (∑ i : Fin 3, aeval (fun k => algebraMap F E (v k)) (pderiv i Φ) * x i) = T := by
    rw [hvE]
  have huR' : R = (u : E) * T := huR.trans (congrArg (fun a : E => (u : E) * a) hTvalue)
  have hT : T ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at huR'
    exact hR huR'
  have hratio : IsAlgebraic J (R / T) := halgF.restrictScalars J
  have hAalg (i : Fin 3) : IsAlgebraic J (A i) := by
    have he := halg i
    simpa only [hj, div_one] using he
  have hIE : (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ} := by
    have he := projectiveFieldPointIdeal_algHom v (IsScalarTower.toAlgHom K F E)
    change (projectiveFieldPointIdeal (E := K) (fun i => algebraMap F E (v i))).toIdeal =
      (projectiveFieldPointIdeal (E := K) v).toIdeal at he
    rw [hvE] at he
    exact he.trans hIF
  exact ⟨Φ, m, hΦ0, hΦ, hm, hirr, hIE, hratio,
    algebraic_direction_and_tangent_ratio_construct_common_finite_field A hAalg T R hT hR hratio⟩

end DimensionFourDependence
