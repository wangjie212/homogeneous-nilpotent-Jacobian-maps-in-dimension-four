import DimensionFourDependence.FullOutputFiber
import DimensionFourDependence.FiberInvariantDataForWitness
import DimensionFourDependence.GenericOutputPoint

/-! # Algebraicity and original invariants in a specified graph coefficient realization -/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "H₀" => (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))
local notation "D₀" => polynomialOutputField H
local notation "Y" => (fun i : Fin 3 => (H₀) (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)

include hrank hY

/-- A graph coefficient realization that retains every original
full-output value makes the same geometric constant field algebraic
over the original graph coefficient field. -/
theorem compatible_full_output_graph_embedding_is_algebraic
    {B : Type u} [Field B] [Algebra D₀ B] [Algebra.IsAlgebraic D₀ B]
    (g : (L) →+* B)
    (hfull : ∀ (d : D₀) (l : L), (l : S₀) = (d : S₀) → g l = algebraMap D₀ B d) :
    letI : Algebra (L) B := g.toAlgebra
    Algebra.IsAlgebraic (L) B := by
  have hr : (rationalJacobian (H₀)).rank = 3 := by
    rw [rationalJacobian_polynomial H]
    exact hrank
  letI : Algebra D₀ (L) := fullOutputCoefficientAlgebra (H₀) hr p hY
  letI : Algebra (L) B := g.toAlgebra
  letI : IsScalarTower D₀ (L) B := IsScalarTower.of_algebraMap_eq (fun d =>
    (hfull d (algebraMap D₀ (L) d) rfl).symm)
  exact Algebra.IsAlgebraic.tower_top (K := D₀) («L» := L)

/-- Any specified original independent output chart and its specified
last output contain all three exact original invariant expressions.
The graph chart is retained rather than chosen again. -/
theorem specified_original_chart_exists_exact_invariant_coefficients
    (hN : IsNilpotent (jac H)) (h : L) (hh : (h : S₀) = (H₀) (p 3)) :
    ∃ c q k : L,
      (c : S₀) = firstFiberInvariantInChart p (Y) hY h ∧
      (q : S₀) = secondFiberInvariant p (Y) hY h c ∧
      (k : S₀) = thirdFiberInvariant p (Y) hY h c q := by
  have hN₀ : IsNilpotent (rationalJacobian (H₀)) := by
    rw [rationalJacobian_polynomial H]
    exact hN.map (algebraMap (MvPolynomial (Fin 4) K) S₀).mapMatrix
  have hr : (rationalJacobian (H₀)).rank = 3 := by
    rw [rationalJacobian_polynomial H]
    exact hrank
  let c : L := ⟨firstFiberInvariantInChart p (Y) hY h,
    firstFiberInvariantInChart_mem_of_rank_three (H₀) hN₀ hr p hY h hh⟩
  let q : L := ⟨secondFiberInvariant p (Y) hY h c,
    secondFiberInvariant_mem_of_nilpotent_rank_three (H₀) hN₀ hr p hY h c hh rfl⟩
  let k : L := ⟨thirdFiberInvariant p (Y) hY h c q,
    thirdFiberInvariant_mem_of_nilpotent_rank_three (H₀) hN₀ hr p hY h c q hh rfl rfl⟩
  exact ⟨c, q, k, rfl, rfl, rfl⟩

end DimensionFourDependence
