import DimensionFourDependence.SegreOriginalFiberWitness
import DimensionFourDependence.SegreFiberCoordinates

/-! # The actual coefficient realization constructs the specified Segre normal form -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 3000000

variable {K E G : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]
  [Field G] [Algebra E G]

attribute [local instance] coefficientFieldScalarTower

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- An actual realization of the original Segre invariants constructs
the full-source radial/transverse decomposition and its exact quadratic
equation over the geometric constants. No chosen isotropic basis or
extension of the coefficient derivations to those constants is supplied. -/
theorem segre_realized_fiber_constructs_radial_transverse_normal_form
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y)
    (c q k : coefficientField (K := K) Y) (x : Fin 4 → G) (y : Fin 4 → E)
    (R : FiberCoefficientRealization (Equiv.refl (Fin 4)) Y hY
      (segreGraphFunction (coefficientCoordinate (K := K) Y)) c q k x y)
    (θ : K) (hweight : coefficientEuler Y hY c = algebraMap K (coefficientField (K := K) Y) θ * c) :
    y 0 ≠ 0 ∧ ∃ τ v w : G,
      (∀ i, x i = τ * algebraMap E G (y i) +
        v * algebraMap E G (segreFirstRulingDirection (y 2 / y 0) i) +
        w * algebraMap E G (segreSecondRulingDirection (y 1 / y 0) i) +
        algebraMap E G ((Pi.single 3 (R.coefficientMap c) : Fin 4 → E) i)) ∧
      algebraMap E G (R.coefficientMap q) =
        algebraMap E G (algebraMap K E θ * R.coefficientMap c) * τ +
        algebraMap E G (R.coefficientMap (coefficientPartial Y hY 1 c)) * v +
        algebraMap E G (R.coefficientMap (coefficientPartial Y hY 2 c)) * w +
        algebraMap E G (1 / y 0) * v * w := by
  let L := coefficientField (K := K) Y
  let U : Fin 3 → L := coefficientCoordinate (K := K) Y
  let δ : Fin 3 → Derivation K L L := coefficientPartial Y hY
  letI : Algebra L G := ((algebraMap E G).comp R.coefficientMap).toAlgebra
  have hbase (z : L) : algebraMap L G z = algebraMap E G (R.coefficientMap z) := rfl
  have hU0 : U 0 ≠ 0 := by
    intro hz
    apply (hY.transcendental 0).ne_zero
    simpa only [U, coefficientCoordinate_coe, IntermediateField.coe_zero] using congrArg (fun a : L => (a : S₀)) hz
  have hcoord (i j : Fin 3) : δ i (U j) = if j = i then 1 else 0 := coefficientPartial_coordinate Y hY i j
  have hy0 : R.coefficientMap (U 0) = y 0 := R.coordinate_image 0
  have hy1 : R.coefficientMap (U 1) = y 1 := R.coordinate_image 1
  have hy2 : R.coefficientMap (U 2) = y 2 := R.coordinate_image 2
  have hY0 : y 0 ≠ 0 := by
    rw [← hy0]
    exact (map_ne_zero R.coefficientMap).mpr hU0
  have htarget (i : Fin 4) : R.coefficientMap (segreGraphTarget U i) = y i := by
    fin_cases i
    · exact hy0
    · exact hy1
    · exact hy2
    · exact R.last_output_image
  have hfirst (i : Fin 4) : R.coefficientMap (segreFirstRulingDirection (U 2 / U 0) i) =
      segreFirstRulingDirection (y 2 / y 0) i := by
    fin_cases i <;> simp [segreFirstRulingDirection, map_div₀, hy0, hy2]
  have hsecond (i : Fin 4) : R.coefficientMap (segreSecondRulingDirection (U 1 / U 0) i) =
      segreSecondRulingDirection (y 1 / y 0) i := by
    fin_cases i <;> simp [segreSecondRulingDirection, map_div₀, hy0, hy1]
  have hsingle (i : Fin 4) : R.coefficientMap ((Pi.single 3 c : Fin 4 → L) i) =
      (Pi.single 3 (R.coefficientMap c) : Fin 4 → E) i := by
    fin_cases i <;> simp
  have hgradient := segre_graph_gradient δ U hcoord hU0
  have hgraph : x 3 = algebraMap L G (-U 1 * U 2 / U 0 ^ 2) * x 0 +
      algebraMap L G (U 2 / U 0) * x 1 + algebraMap L G (U 1 / U 0) * x 2 + algebraMap L G c := by
    have he := R.graph_equation
    change x 3 = (∑ i : Fin 3, algebraMap L G (δ i (segreGraphFunction U)) * x i.castSucc) + algebraMap L G c at he
    simp only [hgradient] at he
    simpa [Fin.sum_univ_succ, add_assoc] using he
  let τ := segreFiberRadialCoordinate U x
  let v := segreFiberFirstTransverse U x
  let w := segreFiberSecondTransverse U x
  have hx := segre_graph_constructs_full_source_radial_transverse_coordinates U hU0 x c hgraph
  have hq : algebraMap L G q = quadraticExpression (fun i => algebraMap L G (δ i c))
      ((derivationHessian δ (segreGraphFunction U)).map (algebraMap L G)) (fun i : Fin 3 => x i.castSucc) :=
    R.quadratic_equation
  have hw : (∑ i, U i * δ i c) = algebraMap K L θ * c := hweight
  have heq := segre_quadratic_fiber_radial_transverse_equation δ U hcoord hU0 x
    (algebraMap K L θ) c q hw hq
  have hθ : R.coefficientMap (algebraMap K L θ) = algebraMap K E θ := R.scalar_image θ
  refine ⟨hY0, τ, v, w, ?_, ?_⟩
  · intro i
    simpa only [hbase, htarget, hfirst, hsecond, hsingle] using hx i
  · simpa only [hbase, map_mul, map_div₀, map_one, hθ, hy0] using heq

end DimensionFourDependence
