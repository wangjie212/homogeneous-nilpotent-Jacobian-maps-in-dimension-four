import DimensionFourDependence.SegreRulingRelativeDimension
import DimensionFourDependence.SegreRulingMatrix

/-! # The actual source output lies in its actual ruling-field kernel -/

namespace DimensionFourDependence

open Matrix
attribute [local instance] coefficientFieldScalarTower

universe u
variable {K : Type u} [Field K] [CharZero K]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The exact original-source inclusion of the ruling parameter
identifies the coefficient-extended ruling matrix with the matrix
formed from the original output ratio. -/
theorem segre_source_output_mem_actual_ruling_field_kernel
    (Q : Fin 4 → S₀) (hY : AlgebraicIndependent K (fun i : Fin 3 => Q i.castSucc))
    (hQ0 : Q 0 ≠ 0) (hquad : Q 0 * Q 3 - Q 1 * Q 2 = 0) (j : Fin 3) (hj : j ≠ 0) :
    (segreRulingMatrix j (segreRulingFieldParameter (fun i : Fin 3 => Q i.castSucc) hY j hj)).map
      (algebraMap (segreSourceRulingParameterHom (fun i : Fin 3 => Q i.castSucc) hY j hj).fieldRange S₀) *ᵥ Q = 0 := by
  let M := (segreSourceRulingParameterHom (fun i : Fin 3 => Q i.castSucc) hY j hj).fieldRange
  let t : M := segreRulingFieldParameter (fun i : Fin 3 => Q i.castSucc) hY j hj
  have ht : algebraMap M S₀ t = Q j.castSucc / Q 0 :=
    segreRulingFieldParameter_source _ hY j hj
  have hm : (segreRulingMatrix j t).map (algebraMap M S₀) = segreRulingMatrix j (Q j.castSucc / Q 0) :=
    (segreRulingMatrix_map (algebraMap M S₀) j t).trans (congrArg (segreRulingMatrix j) ht)
  exact hm.symm ▸ segre_output_mem_ruling_kernel Q hQ0 hquad j hj

end DimensionFourDependence
