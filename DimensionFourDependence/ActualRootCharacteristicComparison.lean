import DimensionFourDependence.GraphDenominatorCharacteristic
import DimensionFourDependence.ExtendedChosenGaussCharacteristic
import DimensionFourDependence.GaussRootNumeratorCoefficients
import DimensionFourDependence.NativeGraphNormalComparison

/-! # The constructed numerator kernel is the actual chosen characteristic line

The original Gauss parameter and closed-cover parameter have their
specified source realizations. Their normals coincide, and the graph
normal differs by its nonzero pivot. The generic second-jet comparison
therefore identifies the canonical root numerator's zero direction with
the actual characteristic matrix, including every coefficient extension.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)

local notation "C₀" => closedGaussParameterField H I
local notation "G₀" => projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)

/-- The original rational Gauss parameter in its actual closed
cover field through the original Gauss-field inclusion. -/
noncomputable def closedGaussOriginalParameterHom (e₀ : RatFunc K ≃ₐ[K] G₀) : RatFunc K →ₐ[K] C₀ :=
  (IsScalarTower.toAlgHom K G₀ C₀).comp e₀.toAlgHom

/-- Differentiation in the actual chosen rational closed-cover parameter. -/
noncomputable def closedGaussCoverDerivation (e : RatFunc K ≃ₐ[K] C₀) : Derivation K C₀ C₀ :=
  fieldDerivationConjugate e (rationalParameterDerivative K)

/-- The original parameter's normal equals the actual closed-field
normal coordinate by coordinate. -/
theorem closedGaussOriginalParameterHom_normal
    (e : RatFunc K ≃ₐ[K] C₀) (e₀ : RatFunc K ≃ₐ[K] G₀) (i : Fin 4) :
    closedGaussOriginalParameterHom H I e₀ (gaussParameterNormal H I e₀ i) =
      actualClosedGaussNormalCovector H I e i := by
  change algebraMap G₀ C₀ (actualGaussRulingMatrix H I e₀ 0 i) = _
  exact actualGaussRulingMatrix_first_row_closed_normal H I e e₀ i

section Graph

variable (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "A" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "A꜀" => fun j => e ((A) j)
local notation "a" => actualClosedGaussNormalCovector H I e (p 3)
local notation "D꜀" => closedGaussCoverDerivation H I e

/-- The actual rational graph slopes retain precisely the original
closed-field graph-gradient coefficients. -/
theorem closedGaussGraphSlope_image_eq_gradient (j : Fin 3) :
    e ((A) j) = actualClosedGaussGraphGradient H I p hY h hh j := by
  unfold closedGaussCoefficientGraphSlope
  rw [e.apply_symm_apply]
  rfl

/-- The original normal and the actual graph normal differ by
exactly the proved nonzero graph pivot inside the closed cover. -/
theorem closedGaussOriginalParameterHom_graph_normal
    (e₀ : RatFunc K ≃ₐ[K] G₀) (i : Fin 4) :
    closedGaussOriginalParameterHom H I e₀ (gaussParameterNormal H I e₀ i) =
      (a) * parameterGraphNormal p (A꜀) i := by
  rw [closedGaussOriginalParameterHom_normal H I e e₀ i,
    actualClosedGaussNormalCovector_eq_graph_pivot_mul H I p hY h hh e i]
  have hA : (A꜀) = actualClosedGaussGraphGradient H I p hY h hh :=
    funext (closedGaussGraphSlope_image_eq_gradient H I p hY h hh e)
  rw [hA]
  rfl

/-- The numerator retained by the actual root construction is
exactly the generic graph second-jet numerator in the cover derivation. -/
theorem closedGaussCanonicalRootNumerator_eq_parameterGraph
    (E : Type u) [Field E] [Algebra C₀ E] :
    closedGaussCanonicalRootNumerator H I p hY h hh e E =
      parameterGraphRootNumerator p (A꜀) (D꜀) (a) (algebraMap C₀ E) := by
  simp only [closedGaussCanonicalRootNumerator, closedGaussRootNumeratorCoefficient,
    parameterGraphRootNumerator, closedGaussCoverDerivation, actualClosedGaussNormalCovector,
    fieldDerivationConjugate_apply]

variable (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "e₀" => actualGaussRulingParameterChoice H I hH hd hind hGauss
local notation "v" => gaussParameterNormal H I (e₀)
local notation "W₀" => LinearMap.ker (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin'
local notation "Cline" => extendedClosedGaussChosenCharacteristicSubspace H I E hH hd hind hGauss

/-- The exact canonical numerator from the actual boundary root
construction vanishes precisely on the actual characteristic line inside
the chosen ruling. Every normalization and parameter-change scalar is proved. -/
theorem actual_canonical_gauss_root_numerator_zero_iff_characteristic
    (b : Fin 4 → E) (hb : b ∈ (W₀)) :
    closedGaussCanonicalRootNumerator H I p hY h hh e E ⬝ᵥ b = 0 ↔ b ∈ (Cline) := by
  let f := closedGaussOriginalParameterHom H I (e₀)
  have hs : (D꜀) (f RatFunc.X) ≠ 0 := rational_cover_parameter_derivative_ne_zero e f
  have hgraph : ∀ i, f ((v) i) = (a) * parameterGraphNormal p (A꜀) i :=
    closedGaussOriginalParameterHom_graph_normal H I p hY h hh e (e₀)
  have hb' : (normalRulingMatrix (rationalParameterDerivative K) (v)).map
      ((algebraMap C₀ E).comp f.toRingHom) *ᵥ b = 0 := hb
  rw [closedGaussCanonicalRootNumerator_eq_parameterGraph]
  change parameterGraphRootNumerator p (A꜀) (D꜀) (a) (algebraMap C₀ E) ⬝ᵥ b = 0 ↔
    (normalCharacteristicMatrix (rationalParameterDerivative K) (v)).map
      ((algebraMap C₀ E).comp f.toRingHom) *ᵥ b = 0
  exact graph_root_numerator_zero_iff_original_characteristic f (D꜀) (v) p (A꜀) (a) hgraph
    (actualClosedGaussNormalCovector_graph_pivot_ne_zero H I p hY h hh e) hs (algebraMap C₀ E) b hb'

end Graph

variable (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

/-- The retained actual second-normal provenance, rather than a
geometric assumption, identifies the numerator kernel with the original
chosen characteristic direction after the actual coefficient extension. -/
theorem actual_gauss_root_numerator_zero_iff_characteristic
    (cN : Fin 4 → E) (hN : HasActualGaussRootNumerator H I E e cN)
    (b : Fin 4 → E)
    (hb : b ∈ LinearMap.ker (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin') :
    cN ⬝ᵥ b = 0 ↔ b ∈ extendedClosedGaussChosenCharacteristicSubspace H I E hH hd hind hGauss := by
  obtain ⟨p, hY, h, hh, rfl⟩ := hN
  exact actual_canonical_gauss_root_numerator_zero_iff_characteristic H I p hY h hh e E hH hd hind hGauss b hb

/-- Every nonzero actual numerator-kernel vector on the ruling
spans precisely the original chosen characteristic line. -/
theorem actual_gauss_root_numerator_zero_direction_spans_characteristic
    (cN : Fin 4 → E) (hN : HasActualGaussRootNumerator H I E e cN)
    (b : Fin 4 → E) (hb0 : b ≠ 0)
    (hb : b ∈ LinearMap.ker (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss).toLin')
    (hzero : cN ⬝ᵥ b = 0) :
    Submodule.span E {b} = extendedClosedGaussChosenCharacteristicSubspace H I E hH hd hind hGauss := by
  exact extendedClosedGaussChosenCharacteristic_span_of_nonzero H I E hH hd hind hGauss b hb0
    ((actual_gauss_root_numerator_zero_iff_characteristic H I E e hH hd hind hGauss cN hN b hb).mp hzero)

end DimensionFourDependence
