import DimensionFourDependence.ExtendedNativeCone
import DimensionFourDependence.ProjectiveConeRootLift
import DimensionFourDependence.NormalizationDivisorNonvertex
import DimensionFourDependence.RadialIntegralUnitObstruction

/-! # Actual positive-weight cone elements have normalization divisors away from the vertex -/

namespace DimensionFourDependence

open AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "s₀" => finSuccEquiv' (0 : Fin 4)
local notation "x₀" => (fun i : Fin 3 => w ((s₀).symm (some i)))
local notation "A₀" => extendedClosedGaussNativeConeAlgebra H I E hH e
local notation "B₀" => normalizationRing A₀
local notation "φ₀" => projectiveConeFractionEmbedding (E := E) x₀

local instance extendedNativeConeNormalizationIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance extendedNativeConeNormalizationAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual four original source coordinates generate the entire
actual cone algebra in their original source labels. -/
theorem extendedClosedGaussNativeConeCoordinate_adjoin :
    Algebra.adjoin E (Set.range (extendedClosedGaussNativeConeCoordinate H I E hH e)) = ⊤ := by
  have hr : Set.range (extendedClosedGaussNativeConeCoordinate H I E hH e) =
      Set.range (projectiveConeCoordinate (E := E) x₀) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(s₀) i, rfl⟩
    · rintro ⟨j, rfl⟩
      refine ⟨(s₀).symm j, ?_⟩
      change projectiveConeCoordinate (E := E) x₀ ((s₀) ((s₀).symm j)) = _
      rw [(s₀).apply_symm_apply]
  exact (congrArg (Algebra.adjoin E) hr).trans (projectiveConeCoordinate_adjoin x₀)

/-- The actual cone normalization is Noetherian, derived from the
original finite-type cone in characteristic zero. -/
theorem extendedClosedGaussNativeConeNormalization_isNoetherian : IsNoetherianRing B₀ := by
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap C₀ E).injective
  let : Algebra.FiniteType E A₀ := extendedClosedGaussNativeConeAlgebra_finiteType H I E hH e
  exact normalizationRing_isNoetherianRing A₀ (K := E)

/-- Every actual height-one prime of the actual cone normalization
avoids some original homogeneous source coordinate. The vertex is
excluded by the original surface dimension, rather than assumed away. -/
theorem extendedClosedGaussNativeConeNormalization_divisor_avoids_coordinate
    (hGauss : gaussImageDimension H I = 1) (Q : Ideal B₀) [Q.IsPrime] (hQ : Q.height = 1) :
    ∃ a : Fin 4, algebraMap A₀ B₀ (extendedClosedGaussNativeConeCoordinate H I E hH e a) ∉ Q := by
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap C₀ E).injective
  let : Algebra.FiniteType E A₀ := extendedClosedGaussNativeConeAlgebra_finiteType H I E hH e
  exact normalization_divisor_avoids_some_original_generator
    (extendedClosedGaussNativeConeCoordinate H I E hH e)
    (extendedClosedGaussNativeConeCoordinate_adjoin H I E hH e)
    (extendedClosedGaussNativeConeAlgebra_trdeg_at_least_two H I E hH e hGauss) Q hQ

/-- The actual cone normalization retains its original radial
rational function by its canonical inclusion into the cone fraction field. -/
noncomputable def extendedClosedGaussNativeConeNormalizationRadialHom : B₀ →+* RatFunc (N).functionField :=
  (φ₀).toRingHom.comp (algebraMap B₀ (FractionRing A₀))

/-- Its entire original cone-algebra restriction is the same
polynomial-valued original coordinate inclusion. -/
theorem extendedClosedGaussNativeConeNormalizationRadialHom_algebraMap (a : A₀) :
    extendedClosedGaussNativeConeNormalizationRadialHom H I E hH e (algebraMap A₀ B₀ a) =
      algebraMap (Polynomial (N).functionField) (RatFunc (N).functionField) (a : Polynomial (N).functionField) := by
  calc
    _ = φ₀ (algebraMap A₀ (FractionRing A₀) a) :=
      congrArg (φ₀) (IsScalarTower.algebraMap_apply A₀ B₀ (FractionRing A₀) a).symm
    _ = _ := projectiveConeFractionEmbedding_algebraMap x₀ a

/-- A given actual cone-normalization element with its nonzero
original radial degree-one value constructs a height-one zero prime
away from the actual vertex. No zero prime or nonvertex coordinate is given. -/
theorem actual_native_radial_cone_element_has_nonvertex_vanishing_divisor
    (hGauss : gaussImageDimension H I = 1) (b : B₀) (u : (N).functionField) (hu : u ≠ 0)
    (hb : extendedClosedGaussNativeConeNormalizationRadialHom H I E hH e b = RatFunc.C u * RatFunc.X) :
    ∃ q : PrimeSpectrum B₀, q.asIdeal.height = 1 ∧ b ∈ q.asIdeal ∧
      ∃ a : Fin 4, algebraMap A₀ B₀ (extendedClosedGaussNativeConeCoordinate H I E hH e a) ∉ q.asIdeal := by
  let : IsNoetherianRing B₀ := extendedClosedGaussNativeConeNormalization_isNoetherian H I E hH e
  let : Algebra.IsIntegral A₀ B₀ :=
    ⟨fun b => integralClosure.isIntegral (R := A₀) (A := FractionRing A₀) b⟩
  have hcomp : (extendedClosedGaussNativeConeNormalizationRadialHom H I E hH e).comp (algebraMap A₀ B₀) =
      (algebraMap (Polynomial (N).functionField) (RatFunc (N).functionField)).comp (A₀).val.toRingHom := by
    apply RingHom.ext
    intro a
    exact extendedClosedGaussNativeConeNormalizationRadialHom_algebraMap H I E hH e a
  obtain ⟨q, hq, hvan⟩ := integral_radial_linear_element_has_vanishing_divisor (A₀).val.toRingHom
    (extendedClosedGaussNativeConeNormalizationRadialHom H I E hH e) hcomp b u hu hb
  exact ⟨q, hq, hvan, extendedClosedGaussNativeConeNormalization_divisor_avoids_coordinate H I E hH e hGauss q.asIdeal hq⟩

end DimensionFourDependence
