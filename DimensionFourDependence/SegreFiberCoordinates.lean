import DimensionFourDependence.SegreProjectiveBoundaryEquations

/-! # Canonical radial and transverse coordinates for an original Segre fiber -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 3000000

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

/-- The target point determined by the three original graph coordinates. -/
def segreGraphTarget (Y : Fin 3 → E) : Fin 4 → E :=
  ![Y 0, Y 1, Y 2, segreGraphFunction Y]

/-- The fixed transverse direction of the ruling with second row ratio `t`. -/
def segreFirstRulingDirection (t : E) : Fin 4 → E := ![0, 1, 0, t]

/-- The fixed transverse direction of the ruling with first row ratio `s`. -/
def segreSecondRulingDirection (s : E) : Fin 4 → E := ![0, 0, 1, s]

def segreFiberRadialCoordinate (Y : Fin 3 → E) (x : Fin 4 → F) : F :=
  x 0 / algebraMap E F (Y 0)

def segreFiberFirstTransverse (Y : Fin 3 → E) (x : Fin 4 → F) : F :=
  x 1 - algebraMap E F (Y 1 / Y 0) * x 0

def segreFiberSecondTransverse (Y : Fin 3 → E) (x : Fin 4 → F) : F :=
  x 2 - algebraMap E F (Y 2 / Y 0) * x 0

/-- The actual graph hyperplane constructs the full original source
decomposition, using the specified radial and two transverse functions. -/
theorem segre_graph_constructs_full_source_radial_transverse_coordinates
    (Y : Fin 3 → E) (hY0 : Y 0 ≠ 0) (x : Fin 4 → F) (c : E)
    (hgraph : x 3 = algebraMap E F (-Y 1 * Y 2 / Y 0 ^ 2) * x 0 +
      algebraMap E F (Y 2 / Y 0) * x 1 + algebraMap E F (Y 1 / Y 0) * x 2 + algebraMap E F c) :
    ∀ i, x i = segreFiberRadialCoordinate Y x * algebraMap E F (segreGraphTarget Y i) +
      segreFiberFirstTransverse Y x * algebraMap E F (segreFirstRulingDirection (Y 2 / Y 0) i) +
      segreFiberSecondTransverse Y x * algebraMap E F (segreSecondRulingDirection (Y 1 / Y 0) i) +
      algebraMap E F ((Pi.single 3 c : Fin 4 → E) i) := by
  have hr : algebraMap E F (Y 0) ≠ 0 := (map_ne_zero (algebraMap E F)).mpr hY0
  intro i
  fin_cases i <;>
    simp [segreFiberRadialCoordinate, segreFiberFirstTransverse, segreFiberSecondTransverse,
      segreGraphTarget, segreGraphFunction, segreFirstRulingDirection, segreSecondRulingDirection,
      map_div₀, map_mul, map_pow, hr]
  all_goals
    try rw [hgraph]
    try simp only [map_div₀, map_neg, map_mul, map_pow]
    field_simp [hr] <;> ring

variable {K : Type*} [Field K] [Algebra K E] [CharZero E]

/-- The actual graph Hessian and output Euler identity give precisely
the quadratic equation in the canonical two transverse functions. -/
theorem segre_quadratic_fiber_radial_transverse_equation
    (δ : Fin 3 → Derivation K E E) (Y : Fin 3 → E)
    (hcoord : ∀ i j, δ i (Y j) = if j = i then 1 else 0) (hY0 : Y 0 ≠ 0)
    (x : Fin 4 → F) (θ c q : E)
    (hweight : (∑ i, Y i * δ i c) = θ * c)
    (hq : algebraMap E F q = quadraticExpression (fun i => algebraMap E F (δ i c))
      ((derivationHessian δ (segreGraphFunction Y)).map (algebraMap E F)) (fun i : Fin 3 => x i.castSucc)) :
    algebraMap E F q = algebraMap E F (θ * c) * segreFiberRadialCoordinate Y x +
      algebraMap E F (δ 1 c) * segreFiberFirstTransverse Y x +
      algebraMap E F (δ 2 c) * segreFiberSecondTransverse Y x +
      algebraMap E F (1 / Y 0) * segreFiberFirstTransverse Y x * segreFiberSecondTransverse Y x := by
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap E F).injective
  have hr : algebraMap E F (Y 0) ≠ 0 := (map_ne_zero (algebraMap E F)).mpr hY0
  have hhalf := segre_graph_half_hessian_pairing_base_change δ Y hcoord hY0 (fun i : Fin 3 => x i.castSucc)
  change algebraMap E F q = (∑ i : Fin 3, algebraMap E F (δ i c) * x i.castSucc) +
    (2 : F)⁻¹ * matrixBilinearPairing ((derivationHessian δ (segreGraphFunction Y)).map (algebraMap E F))
      (fun i : Fin 3 => x i.castSucc) (fun i : Fin 3 => x i.castSucc) at hq
  rw [hhalf] at hq
  rw [hq]
  have hw := congrArg (algebraMap E F) hweight
  simp only [map_sum, map_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hw
  simp only [map_add, map_mul] at hw
  change algebraMap E F (Y 0) * algebraMap E F (δ 0 c) +
    (algebraMap E F (Y 1) * algebraMap E F (δ 1 c) + algebraMap E F (Y 2) * algebraMap E F (δ 2 c)) =
      algebraMap E F θ * algebraMap E F c at hw
  simp only [segreFiberRadialCoordinate, segreFiberFirstTransverse, segreFiberSecondTransverse,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, map_div₀, map_one, map_mul]
  change algebraMap E F (δ 0 c) * x 0 + (algebraMap E F (δ 1 c) * x 1 + algebraMap E F (δ 2 c) * x 2) +
    (x 1 - algebraMap E F (Y 1) / algebraMap E F (Y 0) * x 0) *
      (x 2 - algebraMap E F (Y 2) / algebraMap E F (Y 0) * x 0) / algebraMap E F (Y 0) = _
  field_simp [hr]
  linear_combination (algebraMap E F (Y 0)) ^ 2 * x 0 * hw

end DimensionFourDependence
