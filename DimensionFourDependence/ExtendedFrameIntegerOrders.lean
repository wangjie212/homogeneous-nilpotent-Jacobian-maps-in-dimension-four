import DimensionFourDependence.SchemeIntegerOrderArithmetic
import DimensionFourDependence.RationalFrameGlobalValueArithmetic
import DimensionFourDependence.ExtendedRationalRootMultiplicity
import DimensionFourDependence.ExtendedNormalizationHyperplaneGluing

/-! # Actual native section orders in every original regular frame -/

namespace DimensionFourDependence

open AlgebraicGeometry

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "M" => extendedClosedGaussNormalizationHyperplaneModuleSheaf H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance extendedFrameIntegerOrdersIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance extendedFrameIntegerOrdersNoetherian : IsNoetherian N :=
  extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
local instance extendedFrameIntegerOrdersNonempty (a : Fin 4) : Nonempty (U a) :=
  extendedClosedGaussNormalizationChartOpen_nonempty H I E hH e (finSuccEquiv' a)

/-- The actual regular powered-frame coefficient has exactly the
common rational numerator divided by the original powered frame weight. -/
theorem extendedClosedGaussPowerSectionCoefficient_generic_value {n : ℕ}
    (s : Γ(extendedClosedGaussHyperplanePowerModuleSheaf H I E hH e n, ⊤)) (a : Fin 4) :
    (N).germToFunctionField (U a) (extendedClosedGaussHyperplanePowerSectionCoefficient H I E hH e s a) =
      rationalFrameGlobalSectionValue N (fun a : Fin 4 => U a) (fun a => w a ^ n) s / w a ^ n :=
  rationalFrameGlobalCoefficient_generic_value N (fun a : Fin 4 => U a) (fun a => w a ^ n)
    (extendedClosedGaussNormalizationChartOpen_iSup H I E hH e)
    (fun a => pow_ne_zero n (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e a)) s a

/-- Actual regular original-coordinate transition units preserve
the integer order of every powered-frame rational coefficient. -/
theorem extendedClosedGaussPoweredFrame_integer_order_eq
    (r : (N).functionField) (n : ℕ) (z : N) (i j : Fin 4) (hi : z ∈ U i) (hj : z ∈ U j) :
    (N).ord (r / w i ^ n) z = (N).ord (r / w j ^ n) z := by
  let : Nonempty (U i ⊓ U j : (N).Opens) := ⟨⟨z, hi, hj⟩⟩
  let t := extendedClosedGaussNormalizationHyperplaneTransition H I E hH e i j
  have hv : (N).germToFunctionField (U i ⊓ U j) t = w i / w j :=
    (schemeRationalSectionFunction_eq_generic N (U i ⊓ U j) t ⟨z, hi, hj⟩).symm.trans
      (extendedClosedGaussNormalizationHyperplaneTransition_value H I E hH e i j ⟨z, hi, hj⟩)
  exact scheme_integer_order_powered_frame_eq z (show z ∈ U i ⊓ U j from ⟨hi, hj⟩) t
    (extendedClosedGaussNormalizationHyperplaneTransition_isUnit H I E hH e i j)
    (w i) (w j) r (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e i)
    (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e j) hv n

/-- Actual hyperplane-frame coefficient orders agree in every
original regular coordinate frame at the same point. -/
theorem extendedClosedGaussOriginalFrame_integer_order_eq
    (r : (N).functionField) (z : N) (i j : Fin 4) (hi : z ∈ U i) (hj : z ∈ U j) :
    (N).ord (r / w i) z = (N).ord (r / w j) z := by
  simpa only [pow_one] using extendedClosedGaussPoweredFrame_integer_order_eq H I E hH e r 1 z i j hi hj

/-- Every actual regular powered-frame global section has
nonnegative integer coefficient order in every original frame at an
intrinsic divisor point, including zero coefficients. -/
theorem extendedClosedGaussPowerSection_integer_order_nonneg {n : ℕ}
    (s : Γ(extendedClosedGaussHyperplanePowerModuleSheaf H I E hH e n, ⊤))
    (z : N) (hz : Order.coheight z = 1) (a : Fin 4) (ha : z ∈ U a) :
    0 ≤ (N).ord
      (rationalFrameGlobalSectionValue N (fun a : Fin 4 => U a) (fun a => w a ^ n) s / w a ^ n) z := by
  let : IsDiscreteValuationRing ((N).presheaf.stalk z) :=
    extendedClosedGaussNormalization_divisor_stalk_isDVR H I E hH e z hz
  let c := extendedClosedGaussHyperplanePowerSectionCoefficient H I E hH e s a
  have hv := (Scheme.algebraMap_germ_eq_germToFunctionField N ha c).trans
    (extendedClosedGaussPowerSectionCoefficient_generic_value H I E hH e s a)
  exact hv ▸ scheme_regular_integer_order_nonneg z hz ((N).presheaf.germ (U a) z ha c)

variable (hGauss : gaussImageDimension H I = 1)
  (p q : MvPolynomial (Fin 4) K) {D : ℕ}
  (hq0 : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
  (ht : closedGaussParameterSourceHom H I e RatFunc.X =
    algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)

include hGauss hq0 hrel hpH hqH ht in
/-- Every nonzero actual native global hyperplane section has
pencil-degree-bounded integer multiplicity in every original regular
coordinate frame at every intrinsic divisor point. -/
theorem actual_native_pencil_global_section_every_frame_multiplicity_bound
    (s : Γ(M, ⊤)) (hs : s ≠ 0) (z : N) (hz : Order.coheight z = 1)
    (a : Fin 4) (ha : z ∈ U a) :
    0 ≤ (N).ord (extendedClosedGaussHyperplaneGlobalValue H I E hH e s / w a) z ∧
      (N).ord (extendedClosedGaussHyperplaneGlobalValue H I E hH e s / w a) z ≤ (D : ℤ) := by
  obtain ⟨b, hb, hbound⟩ := actual_native_pencil_global_section_all_divisors_multiplicity_bound
    H I E hH e hGauss p q hq0 hrel hpH hqH ht s hs z hz
  have hval := (Scheme.algebraMap_germ_eq_germToFunctionField N hb
    (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s b)).trans
      (rationalFrameGlobalCoefficient_generic_value N (fun a : Fin 4 => U a) w
        (extendedClosedGaussNormalizationChartOpen_iSup H I E hH e)
        (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e) s b)
  dsimp only at hbound
  rw [hval] at hbound
  exact (extendedClosedGaussOriginalFrame_integer_order_eq H I E hH e _ z a b ha hb).symm ▸ hbound

end DimensionFourDependence
