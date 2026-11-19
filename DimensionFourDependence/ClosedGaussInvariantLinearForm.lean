import DimensionFourDependence.ClosedGaussCoefficientTensor
import DimensionFourDependence.ExtendedNativeLinearCombinations

/-! # The actual first invariant is an original source linear form over the closed Gauss field -/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "C₀" => closedGaussParameterField H I

/-- Every actual graph gradient coordinate, as an element of the
original closed Gauss field inside the original source. -/
noncomputable def actualClosedGaussGraphGradient (i : Fin 3) : C₀ :=
  ⟨(coefficientPartial (Y) hY i h : S₀),
    actual_graph_gradient_mem_closed_gauss_field H I p hY h hh i⟩

/-- The actual first-invariant covector in the original four source
coordinates, with all coefficients in the actual closed Gauss field. -/
noncomputable def actualClosedGaussFirstInvariantCovector : Fin 4 → C₀ :=
  Fin.snoc (fun i => -actualClosedGaussGraphGradient H I p hY h hh i) 1 ∘ p.symm

/-- The specified source linear form evaluates to the actual first
fiber invariant, retaining the original coordinate labels. -/
theorem actualClosedGaussFirstInvariantCovector_source_value :
    aeval (rationalCoordinate (K := K) (n := 4))
      (linearFormPolynomial (actualClosedGaussFirstInvariantCovector H I p hY h hh)) =
        firstFiberInvariantInChart p (Y) hY h := by
  let ν := actualClosedGaussFirstInvariantCovector H I p hY h hh
  simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X]
  rw [← Equiv.sum_comp p (fun j => algebraMap C₀ S₀ (ν j) * rationalCoordinate (K := K) j),
    Fin.sum_univ_castSucc]
  simp only [ν, actualClosedGaussFirstInvariantCovector, Function.comp_apply,
    Equiv.symm_apply_apply, Fin.snoc_castSucc, Fin.snoc_last, map_neg, map_one,
    one_mul, neg_mul, Finset.sum_neg_distrib]
  change -(∑ i : Fin 3, (coefficientPartial (Y) hY i h : S₀) *
    rationalCoordinate (K := K) (p i.castSucc)) + rationalCoordinate (K := K) (p 3) = _
  unfold firstFiberInvariantInChart
  ring

/-- The actual source covector is nonzero: its selected last
coordinate is the unit coefficient. -/
theorem actualClosedGaussFirstInvariantCovector_ne_zero :
    actualClosedGaussFirstInvariantCovector H I p hY h hh ≠ 0 := by
  intro hz
  have he := congrFun hz (p 3)
  have hlast : actualClosedGaussFirstInvariantCovector H I p hY h hh (p 3) = 1 := by
    simp only [actualClosedGaussFirstInvariantCovector, Function.comp_apply,
      Equiv.symm_apply_apply]
    rfl
  exact one_ne_zero (hlast.symm.trans he)

end DimensionFourDependence
