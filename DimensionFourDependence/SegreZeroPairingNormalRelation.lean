import DimensionFourDependence.SegreZeroPairingSourceInvariants
import DimensionFourDependence.SegreSplitLaplacian

/-! # The actual vanishing first invariant gives the original determinant normal relation -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] coefficientFieldScalarTower

set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual zero first invariant is the original polynomial normal
identity grad(Delta)(X) dot H(X)=0. No differential normal relation is supplied. -/
theorem original_segre_zero_first_invariant_constructs_polynomial_normal_relation
    (H : Fin 4 → R₀) (hind : ¬ComponentsDependent H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (hY : AlgebraicIndependent K (segreOriginalOutputTriple H))
    (hc : firstFiberInvariantInChart (Equiv.refl (Fin 4)) (segreOriginalOutputTriple H) hY
      (segreOriginalCoefficientGraph H) = 0) : segreNormalPairing H = 0 := by
  let L := coefficientField (K := K) (segreOriginalOutputTriple H)
  let U : Fin 3 → L := coefficientCoordinate (K := K) (segreOriginalOutputTriple H)
  let δ : Fin 3 → Derivation K L L := coefficientPartial (segreOriginalOutputTriple H) hY
  let x : Fin 4 → S₀ := rationalCoordinate (K := K)
  let a := algebraMap R₀ S₀ (H 0)
  let b := algebraMap R₀ S₀ (H 1)
  let c := algebraMap R₀ S₀ (H 2)
  let e := algebraMap R₀ S₀ (H 3)
  have ha : a ≠ 0 := original_segre_first_output_ne_zero H hind
  have hU0 : U 0 ≠ 0 := by
    intro hz
    apply ha
    exact congrArg (fun z : L => (z : S₀)) hz
  have hcoord (i j : Fin 3) : δ i (U j) = if j = i then 1 else 0 :=
    coefficientPartial_coordinate (segreOriginalOutputTriple H) hY i j
  have hgraph : x 3 = ∑ i : Fin 3, algebraMap L S₀ (δ i (segreGraphFunction U)) * x i.castSucc :=
    sub_eq_zero.mp hc
  have hgraph' : x 3 = -(b * c) / a ^ 2 * x 0 + c / a * x 1 + b / a * x 2 := by
    rw [hgraph]
    simp only [segre_graph_gradient δ U hcoord hU0, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one, map_div₀, map_mul, map_neg, map_pow, add_zero]
    change -b * c / a ^ 2 * x 0 + (c / a * x 1 + b / a * x 2) = _
    ring
  have hquad : a * e - b * c = 0 := by
    have he := congrArg (algebraMap R₀ S₀) hSegre
    simpa only [map_sub, map_mul, map_zero] using he
  have he : e = b * c / a := by
    apply (eq_div_iff ha).mpr
    simpa only [mul_comm] using sub_eq_zero.mp hquad
  have hnormal : x 3 * a - x 2 * b - x 1 * c + x 0 * e = 0 := by
    rw [hgraph', he]
    field_simp [ha]
    ring
  apply IsFractionRing.injective R₀ S₀
  simpa only [segreNormalPairing, map_add, map_sub, map_mul, map_zero,
    a, b, c, e, x, rationalCoordinate] using hnormal

end DimensionFourDependence
