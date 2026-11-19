import DimensionFourDependence.FullOutputField
import DimensionFourDependence.ProjectivePointCoefficientComparison

/-! # Original generic-fiber Hilbert functions are independent of the chosen output chart -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] [CharZero K]
  (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
  (hrank : (rationalJacobian H).rank = 3)

include hrank

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "L₀" p:max => coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc))

/-- Two actual independent output charts have exactly the same
relatively closed coefficient subfield inside the original source field. -/
theorem original_coefficient_chart_field_eq
    (p q : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
    (hZ : AlgebraicIndependent K (fun i : Fin 3 => H (q i.castSucc))) :
    (L₀ p).restrictScalars K = (L₀ q).restrictScalars K := by
  ext x
  exact (fullOutput_algebraic_iff_coefficientField H hrank p hY x).symm.trans
    (fullOutput_algebraic_iff_coefficientField H hrank q hZ x)

/-- Both original output charts give exactly the same Hilbert
function for every original projective coordinate vector. -/
theorem original_coefficient_chart_projective_hilbert_eq
    (p q : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
    (hZ : AlgebraicIndependent K (fun i : Fin 3 => H (q i.castSucc)))
    {σ : Type*} [Finite σ] (x : σ → S₀) (n : ℕ) :
    projectiveHilbertFunction (projectiveFieldPointIdeal (E := L₀ p) x).toIdeal n =
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := L₀ q) x).toIdeal n := by
  have he := original_coefficient_chart_field_eq H hrank p q hY hZ
  change projectiveHilbertFunction
    (projectiveFieldPointIdeal (E := (L₀ p).restrictScalars K) x).toIdeal n =
    projectiveHilbertFunction
      (projectiveFieldPointIdeal (E := (L₀ q).restrictScalars K) x).toIdeal n
  rw [he]

/-- The original full affine generic-fiber degree exists in every
specified independent output chart, not just in the chart chosen by
the auxiliary intersection-equation witness. -/
theorem original_full_fiber_curve_degree_exists_in_every_output_chart
    (hN : IsNilpotent (rationalJacobian H))
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc))) :
    ∃ D : ℕ, D ≤ 6 ∧ HasCurveHilbertDegree (projectiveConeIdeal (L := L₀ p)
      (rationalCoordinate (K := K) (n := 4))) D := by
  obtain ⟨W⟩ := exists_projective_fiber_equation_witness H hN hrank
  obtain ⟨D, hD6, hD⟩ := fiber_witness_full_source_degree H hN hrank W
  refine ⟨D, hD6, ?_⟩
  have he (n : ℕ) : projectiveHilbertFunction (projectiveConeIdeal (L := L₀ p)
      (rationalCoordinate (K := K) (n := 4))) n =
      projectiveHilbertFunction (projectiveConeIdeal (L := L₀ W.affine.chart)
        (rationalCoordinate (K := K) (n := 4))) n :=
    original_coefficient_chart_projective_hilbert_eq H hrank p W.affine.chart hY W.affine.independent
      (fun i : Option (Fin 4) => i.elim 1 (rationalCoordinate (K := K) (n := 4))) n
  simpa only [HasCurveHilbertDegree, he] using hD

end DimensionFourDependence
