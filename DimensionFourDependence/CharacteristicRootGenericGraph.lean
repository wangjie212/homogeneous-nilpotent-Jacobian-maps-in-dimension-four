import DimensionFourDependence.CharacteristicRootPencilBasePoint
import DimensionFourDependence.CharacteristicRootStalkSeparation
import DimensionFourDependence.SeparatedPencilGraphKernel
import DimensionFourDependence.CharacteristicPencilRegularZero

/-! # The actual characteristic-root base point has a free generic pencil parameter -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  [Module.Finite (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "C₀" => closedGaussParameterField H I
local notation "T₀" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "f" => extendedClosedGaussNormalizationProjectiveMap H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH
  (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss 0
local notation "Lₜ" => ∑ j, algebraMap E (N).functionField ((ν₀) j) * (w) j
local notation "z₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q
local notation "ha₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q
local notation "ρ₀" c:max r:max hroot:max => extendedClosedGaussOutputLinearRootSection H I E hH e
  c r (Nat.lt_trans Nat.zero_lt_one hd) hroot
local notation "L₀" => extendedClosedGaussInputLinearSection H I E hH e (ν₀)
local notation "t₀" r:max => nativeCharacteristicPencilValue H I E hH e
  (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r

local instance characteristicRootGenericGraphIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance characteristicRootGenericGraphNoetherian : IsNoetherian N :=
  extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
noncomputable local instance characteristicRootGenericGraphAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Each actual characteristic-root divisor constructs a point on
that same branch where the actual pencil's graph has a completely free
residue parameter. The point, chart, common zeros, and zero/pole
separation are all constructed from the original root factorization. -/
theorem actual_characteristic_root_divisor_constructs_free_generic_graph
    (cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval (w) ((O) cS))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss cN r)
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (hzero : (N).presheaf.germ (U a) (z₀ a q) (ha₀ a q)
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (ρ₀ cS r hroot) a) ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk (z₀ a q))) :
    ∃ z : N, (z₀ a q) ⤳ z ∧ (z₀ a q) ≠ z ∧
      ∃ (b : Fin 4) (hb : z ∈ U b),
        (N).presheaf.germ (U b) z hb
          (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (ρ₀ cS r hroot) b) ∈
            IsLocalRing.maximalIdeal ((N).presheaf.stalk z) ∧
        (N).presheaf.germ (U b) z hb
          (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (L₀) b) ∈
            IsLocalRing.maximalIdeal ((N).presheaf.stalk z) ∧
        RingHom.ker (Polynomial.aeval (t₀ r) :
          Polynomial ((N).presheaf.stalk z) →ₐ[(N).presheaf.stalk z] (N).functionField).toRingHom ≤
          RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue ((N).presheaf.stalk z))) := by
  obtain ⟨z, hxz, hne, b, hb, hρz, hLz⟩ :=
    actual_characteristic_root_divisor_constructs_pencil_base_point
      H I E hH e hd hind hGauss cS cN r hroot hfactor a q hq hzero
  let R := (N).presheaf.stalk z
  letI : IsIntegrallyClosed R :=
    extendedClosedGaussNormalizationScheme_stalk_isIntegrallyClosed H I E hH e z
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
  letI : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap C₀ E).injective
  let hx : (z₀ a q) ∈ U b := hxz.mem_open (U b).isOpen hb
  let φ : R →+* (N).presheaf.stalk (z₀ a q) := ((N).presheaf.stalkSpecializes hxz).hom
  let A : R := (N).presheaf.germ (U b) z hb
    (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (ρ₀ cS r hroot) b)
  let B : R := (N).presheaf.germ (U b) z hb
    (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (L₀) b)
  have hmap (v : Γ(N, U b)) : φ ((N).presheaf.germ (U b) z hb v) =
      (N).presheaf.germ (U b) (z₀ a q) hx v :=
    ConcreteCategory.congr_hom ((N).presheaf.germ_stalkSpecializes hb hxz) v
  have hAx : φ A ∈ IsLocalRing.maximalIdeal ((N).presheaf.stalk (z₀ a q)) := by
    rw [hmap]
    exact (native_output_linear_root_zero_iff_source_equation H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) cS r hroot (z₀ a q) b hx).mpr
        ((native_output_linear_root_zero_iff_source_equation H I E hH e
          (Nat.lt_trans Nat.zero_lt_one hd) cS r hroot (z₀ a q) a (ha₀ a q)).mp hzero)
  have hnot := characteristic_root_and_tangent_plane_have_no_common_divisor
    H I E hH e hd hind hGauss cS cN r hroot hfactor a q hq hzero
  have hBx : IsUnit (φ B) := by
    rw [hmap]
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hLx
    have hEq := (native_input_linear_section_zero_iff_source_equation
      H I E hH e (ν₀) (z₀ a q) b hx).mp hLx
    exact hnot ((native_input_linear_section_zero_iff_source_equation
      H I E hH e (ν₀) (z₀ a q) a (ha₀ a q)).mpr hEq)
  have hAv : algebraMap R (N).functionField A = r / (w) b := by
    rw [extendedClosedGaussHyperplaneGlobalCoefficient_germ_value,
      extendedClosedGaussOutputLinearRootSection_value]
  have hBv : algebraMap R (N).functionField B = (Lₜ) / (w) b := by
    rw [extendedClosedGaussHyperplaneGlobalCoefficient_germ_value,
      extendedClosedGaussInputLinearSection_value]
  have hA0 : A ≠ 0 := by
    intro he
    have hz0 : r / (w) b = 0 :=
      hAv.symm.trans ((congrArg (algebraMap R (N).functionField) he).trans (map_zero _))
    exact div_ne_zero hr (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e b) hz0
  have hgraph := separated_local_pencil_graph_kernel_le_residue_polynomial_kernel
    (k := E) (F := (N).functionField) φ A B hA0 hAx hBx hLz
      (fun Q hQ hBQ => characteristic_root_avoids_tangent_plane_height_one_stalk_prime
        H I E hH e hd hind hGauss cS cN r hroot hfactor z b hb Q hQ hBQ)
  have hv : algebraMap R (N).functionField A / algebraMap R (N).functionField B = (t₀ r) := by
    rw [hAv, hBv]
    exact div_div_div_cancel_right₀
      (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e b) r (Lₜ)
  refine ⟨z, hxz, hne, b, hb, hρz, hLz, ?_⟩
  exact (congrArg (fun t : (N).functionField =>
    RingHom.ker (Polynomial.aeval t : Polynomial R →ₐ[R] (N).functionField).toRingHom ≤
      RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue R))) hv).mp hgraph

end DimensionFourDependence
