import DimensionFourDependence.ActualUniformSimpleBoundaryDirection
import DimensionFourDependence.GraphBoundaryProportionality

/-! # Every prime of the actual extended infinity section is the same fixed point

The actual normalized coordinate field of each infinity prime is
algebraic over the original fiber coefficients. Apply the uniform
boundary theorem there, using the same finite root forms and dual pair.
The original graph equation determines the fourth direction coordinate,
so the full projective prime is the original rational fixed point.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "x" => rationalCoordinate (K := K) (n := 4)
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh e
local notation "A₀" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "y₀" => coefficientCoordinate (K := K) (Y)
local notation "n₀" => parametricRulingDenominator (f₀) (A₀) (y₀)

variable (F : Type u) [Field F]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) F]
    [Algebra K F]
    [IsScalarTower K (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) F]
    [Algebra.IsAlgebraic (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) F]

local notation "gF" => IsScalarTower.toAlgHom K (L) F
local notation "fF" => (gF).comp (f₀)
local notation "yF" => fun i => (gF) ((y₀) i)
local notation "AF" => fun i => (fF) ((A₀) i)

include hrank

/-- In the independent-root case, every actual projective prime of
the original full-fiber infinity section after the specified algebraic
coefficient extension is the same constructed rational fixed point.
No support statement, closed-point classification or algebraicity of
prime coordinate fields is supplied as an auxiliary hypothesis. -/
theorem actual_extended_full_fiber_simple_root_infinity_support_single_point
    {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (c q k : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q)
    (C : IntermediateField (fF).fieldRange F) [Module.Finite (fF).fieldRange C]
    (m s b a : Fin 3 → C)
    (hpair : LinearIndependent C ![rulingFormRestriction (finiteParameterGraphRuling (fF) C (A₀)) m,
      rulingFormRestriction (finiteParameterGraphRuling (fF) C (A₀)) s])
    (hb : b ∈ finiteParameterGraphRuling (fF) C (A₀)) (ha : a ∈ finiteParameterGraphRuling (fF) C (A₀))
    (hmb : m ⬝ᵥ b = 1) (hsb : s ⬝ᵥ b = 0) (hma : m ⬝ᵥ a = 0) (hsa : s ⬝ᵥ a = 1)
    (rho : F) (hrho : rho ≠ 0)
    (hprod : (gF) (n₀) * (gF) c = ((fun i => (m i : F)) ⬝ᵥ (yF)) * rho)
    (hroot : rho ^ d = (fun i => (s i : F)) ⬝ᵥ (yF)) :
    ∃ hbF : (fun i => (b i : F)) ≠ 0,
      ∀ z : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) F),
        Ideal.map (MvPolynomial.map (algebraMap (L) F)) (projectiveConeIdeal («L» := L) (x)) ⊔
          Ideal.span ({X none} : Set (MvPolynomial (Option (Fin 4)) F)) ≤ z.asHomogeneousIdeal.toIdeal →
        z = projectiveFieldPoint (E := F)
          (fun j : Option (Fin 4) => j.elim 0 (graphBoundaryDirection p (AF) (fun i => (b i : F))))
          (by
            intro hzero
            apply graphBoundaryDirection_ne_zero p (AF) (fun i => (b i : F)) hbF
            funext i
            exact congrFun hzero (some i)) := by
  have hmbF : (fun i => (m i : F)) ⬝ᵥ (fun i => (b i : F)) = 1 := by
    simpa only [dotProduct, map_sum, map_mul, map_one, IntermediateField.algebraMap_apply] using
      congrArg (algebraMap C F) hmb
  have hbF : (fun i => (b i : F)) ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hmbF
    exact zero_ne_one hmbF
  refine ⟨hbF, ?_⟩
  intro z hsection
  have hext : Ideal.map (MvPolynomial.map (algebraMap (L) F)) (projectiveConeIdeal («L» := L) (x)) ≤
      z.asHomogeneousIdeal.toIdeal := le_sup_left.trans hsection
  have hinfinity : X none ∈ z.asHomogeneousIdeal :=
    hsection ((show Ideal.span ({X none} : Set (MvPolynomial (Option (Fin 4)) F)) ≤
      Ideal.map (MvPolynomial.map (algebraMap (L) F)) (projectiveConeIdeal («L» := L) (x)) ⊔
        Ideal.span {X none} from le_sup_right) (Ideal.subset_span (by simp)))
  obtain ⟨j, hj⟩ := projective_infinity_prime_exists_direction_coordinate_not_mem z hinfinity
  let R := projectivePrimeRatioField z (some j)
  let w := projectivePrimeRatioCoordinate z (some j)
  let : IsScalarTower K (L) R := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply K F R, IsScalarTower.algebraMap_apply (L) F R,
      ← IsScalarTower.algebraMap_apply K (L) F])
  let : Algebra.IsAlgebraic F R := actual_full_infinity_prime_normalized_field_isAlgebraic H hrank p hY F
    (by omega) hH hN hind I hGauss h c q hh hc hq z hext hinfinity j hj
  let : Algebra.IsAlgebraic (L) R := Algebra.IsAlgebraic.trans (L) F R
  have hw0 : w ≠ 0 := projectivePrimeRatioCoordinate_ne_zero z (some j) hj
  have hwj : w (some j) = 1 := projectivePrimeRatioCoordinate_self z (some j) hj
  have hwzero : w none = 0 := projectivePrimeRatioCoordinate_zero_of_mem z (some j) none hinfinity
  have hpoint := normalized_extended_projective_prime_mem_original_closure (x) z hext (some j) hj
  obtain ⟨t, ht, hrep⟩ := actual_normalized_boundary_multiple_of_same_finite_simple_root H hrank I p hY h hh e F R
    hd hH hN hind hGauss c q k hc hq hk C m s b a hpair hb ha hmb hsb hma hsa
    rho hrho hprod hroot w hw0 hpoint hwzero j hwj
  have hlinear := actual_full_fiber_boundary_graph_linear_equation H p hY h c hc R w hw0 hpoint hwzero
  have hAF (i : Fin 3) : algebraMap F R ((AF) i) = algebraMap (L) R (coefficientPartial (Y) hY i h) := by
    change algebraMap F R (algebraMap (L) F ((f₀) ((A₀) i))) = _
    rw [← IsScalarTower.algebraMap_apply (L) F R, closedGaussCoefficientGraphSlope_value]
  have hlinearF : w (some (p 3)) =
      (fun i => algebraMap F R ((AF) i)) ⬝ᵥ (fun i : Fin 3 => w (some (p i.castSucc))) := by
    simpa only [hAF, dotProduct] using hlinear
  have hfullrep := graph_boundary_direction_proportional_of_first_coordinates p (AF) (fun i => (b i : F))
    (algebraMap F R) (fun i : Fin 4 => w (some i)) t hlinearF hrep
  have hfull0 : (fun i : Fin 4 => w (some i)) ≠ 0 := by
    intro hzero
    have he := congrFun hzero j
    rw [hwj] at he
    exact one_ne_zero he
  have hgraph0 := graphBoundaryDirection_ne_zero p (AF) (fun i => (b i : F)) hbF
  have hcoord : w = (fun i : Option (Fin 4) => i.elim 0 (fun j => w (some j))) := by
    funext i
    cases i with
    | none => exact hwzero
    | some i => rfl
  have hvec0 : (fun i : Option (Fin 4) => i.elim 0 (fun j => w (some j))) ≠ 0 := by
    rw [← hcoord]
    exact hw0
  calc
    z = projectiveFieldPoint (E := F) w hw0 := (projectivePrimeRatioCoordinate_represents z (some j) hj).symm
    _ = projectiveFieldPoint (E := F) (fun i : Option (Fin 4) => i.elim 0 (fun j => w (some j))) hvec0 :=
      projectiveFieldPoint_eq_of_coordinate_eq _ _ hw0 hvec0 hcoord
    _ = _ := projective_infinity_point_eq_of_mapped_direction_multiple
      (graphBoundaryDirection p (AF) (fun i => (b i : F))) (fun i : Fin 4 => w (some i))
      hgraph0 hfull0 t ht hfullrep

end DimensionFourDependence
