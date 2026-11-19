import DimensionFourDependence.ExtendedNativeConeNormalization
import DimensionFourDependence.ActualGaussRootUnitCoefficients

/-! # The paper's actual rational root and U are regular elements on its actual cone normalization -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
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

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "s₀" => finSuccEquiv' (0 : Fin 4)
local notation "x₀" => (fun i : Fin 3 => w ((s₀).symm (some i)))
local notation "A₀" => extendedClosedGaussNativeConeAlgebra H I E hH e
local notation "B₀" => normalizationRing A₀
local notation "g₀" => extendedClosedGaussNormalization_original_affine_field_top H I E hH e

local instance extendedNativeConeRootsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance extendedNativeConeRootsAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Relabeling the original four coordinates to the original affine
cone frame retains every original source polynomial value. -/
theorem extendedClosedGaussNativeCone_reindexed_polynomial_value
    (P : MvPolynomial (Fin 4) E) :
    aeval (fun i : Option (Fin 3) => i.elim 1 x₀) (rename (s₀) P) = aeval w P := by
  rw [aeval_rename]
  exact congrArg (fun z : Fin 4 → (N).functionField => aeval z P)
    (funext (extendedClosedGaussNativeCone_option_coordinate H I E hH e))

/-- The actual radial homogenization of a native point-field value
in the paper's actual cone fraction field. -/
noncomputable def extendedClosedGaussNativeConeRadialLift (u : (N).functionField) : FractionRing A₀ :=
  projectiveConeRadialLift x₀ g₀ u

theorem extendedClosedGaussNativeConeRadialLift_value (u : (N).functionField) :
    projectiveConeFractionEmbedding (E := E) x₀
      (extendedClosedGaussNativeConeRadialLift H I E hH e u) = RatFunc.C u * RatFunc.X :=
  projectiveConeRadialLift_value x₀ g₀ u

/-- Every actual native rational root of an original positive-degree
homogeneous source form lifts regularly to the actual cone normalization. -/
theorem extendedClosedGaussNativeConeRadialLift_root_mem_normalization
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n) (hn : 0 < n)
    (r : (N).functionField) (hroot : r ^ n = aeval w P) :
    extendedClosedGaussNativeConeRadialLift H I E hH e r ∈ B₀ :=
  projectiveConeRadialLift_root_mem_normalization x₀ g₀ (rename (s₀) P) hP.rename_isHomogeneous hn r
    (hroot.trans (extendedClosedGaussNativeCone_reindexed_polynomial_value H I E hH e P).symm)

/-- The actual global section U, with its original root and original
input linear form, is regular over the whole actual cone algebra. -/
theorem extendedClosedGaussNativeConeRadialLift_root_combination_mem_normalization
    (ν c : Fin 4 → E) (r : (N).functionField) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E c)) (α β : E) :
    extendedClosedGaussNativeConeRadialLift H I E hH e
      (extendedClosedGaussHyperplaneGlobalValue H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e ν c r hd hroot α β)) ∈ B₀ := by
  let Q := rename (s₀) (linearFormPolynomial ν)
  let P := rename (s₀) (extendedClosedGaussOutputLinearPolynomial H I E c)
  have hQ : Q.IsHomogeneous 1 :=
    (extendedClosedGaussInputLinearPolynomial_homogeneous E ν).rename_isHomogeneous
  have hP : P.IsHomogeneous d :=
    (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH c).rename_isHomogeneous
  have hR : r ^ d = aeval (fun i : Option (Fin 3) => i.elim 1 x₀) P :=
    hroot.trans (extendedClosedGaussNativeCone_reindexed_polynomial_value H I E hH e _).symm
  have hi := projectiveConeRadialLift_root_combination_mem_normalization x₀ g₀ Q hQ P hP hd r hR α β
  have hlinear : aeval (fun i : Option (Fin 3) => i.elim 1 x₀) Q =
      ∑ i, algebraMap E (N).functionField (ν i) * w i := by
    calc
      _ = aeval w (linearFormPolynomial ν) :=
        extendedClosedGaussNativeCone_reindexed_polynomial_value H I E hH e _
      _ = _ := by simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X]
  have hu : extendedClosedGaussHyperplaneGlobalValue H I E hH e
      (extendedClosedGaussRootCombinationSection H I E hH e ν c r hd hroot α β) =
        algebraMap E (N).functionField α * aeval (fun i : Option (Fin 3) => i.elim 1 x₀) Q +
          algebraMap E (N).functionField β * r :=
    (extendedClosedGaussRootCombinationSection_value H I E hH e ν c r hd hroot α β).trans
      (congrArg (fun v : (N).functionField => algebraMap E (N).functionField α * v +
        algebraMap E (N).functionField β * r) hlinear.symm)
  exact (congrArg (fun u : (N).functionField =>
    extendedClosedGaussNativeConeRadialLift H I E hH e u ∈ B₀) hu).to_iff.mpr hi

/-- The paper's actual root-combination section as an actual regular
element of the actual cone normalization. -/
noncomputable def extendedClosedGaussNativeConeRootCombination
    (ν c : Fin 4 → E) (r : (N).functionField) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E c)) (α β : E) : B₀ :=
  ⟨extendedClosedGaussNativeConeRadialLift H I E hH e
      (extendedClosedGaussHyperplaneGlobalValue H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e ν c r hd hroot α β)),
    extendedClosedGaussNativeConeRadialLift_root_combination_mem_normalization H I E hH e ν c r hd hroot α β⟩

/-- That constructed cone-normalization element retains the exact
original section value with radial degree one. -/
theorem extendedClosedGaussNativeConeRootCombination_value
    (ν c : Fin 4 → E) (r : (N).functionField) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E c)) (α β : E) :
    extendedClosedGaussNativeConeNormalizationRadialHom H I E hH e
      (extendedClosedGaussNativeConeRootCombination H I E hH e ν c r hd hroot α β) =
        RatFunc.C (extendedClosedGaussHyperplaneGlobalValue H I E hH e
          (extendedClosedGaussRootCombinationSection H I E hH e ν c r hd hroot α β)) * RatFunc.X :=
  projectiveConeRadialLift_value x₀ g₀ _

/-- The original nonzero root and actual product-power equation
construct a zero divisor of the actual homogenized U away from the
actual cone vertex. No zero prime, nonvertex coordinate or image
hypothesis is supplied. Transfer to the projective normalization is separate. -/
theorem actual_native_root_combination_cone_nonvertex_vanishing_divisor
    (hGauss : gaussImageDimension H I = 1)
    (ν cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS)) (α β : E)
    (hprod : extendedClosedGaussHyperplaneGlobalValue H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β) *
          aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) = r ^ (d + 1)) :
    ∃ q : PrimeSpectrum B₀, q.asIdeal.height = 1 ∧
      extendedClosedGaussNativeConeRootCombination H I E hH e ν cS r hd hroot α β ∈ q.asIdeal ∧
      ∃ a : Fin 4, algebraMap A₀ B₀ (extendedClosedGaussNativeConeCoordinate H I E hH e a) ∉ q.asIdeal := by
  have hu : extendedClosedGaussHyperplaneGlobalValue H I E hH e
      (extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β) ≠ 0 :=
    (mul_ne_zero_iff.mp (hprod ▸ pow_ne_zero (d + 1) hr)).1
  exact actual_native_radial_cone_element_has_nonvertex_vanishing_divisor H I E hH e hGauss
    (extendedClosedGaussNativeConeRootCombination H I E hH e ν cS r hd hroot α β) _ hu
    (extendedClosedGaussNativeConeRootCombination_value H I E hH e ν cS r hd hroot α β)

end DimensionFourDependence
