import DimensionFourDependence.ScaledPlaneNormalizedBaseBranch
import DimensionFourDependence.NativePolynomialGermPointEquations
import DimensionFourDependence.ProjectiveVertexLineNormalSection
import DimensionFourDependence.ActualVertexStalkDenominatorPoles
import DimensionFourDependence.LocalZeroPoleCriterion

/-! # Original scaled-plane base branches construct general levels through the vertex -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory Topology
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hind : ¬ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "T₀" => FractionRing (MvPolynomial (Fin 4) K) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "V" => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' (Fin.last 3))
local notation "f" => extendedClosedGaussNormalizationProjectiveMap H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "germ" P:max z:max hz:max => extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z (Fin.last 3) hz

local instance scaledPlaneVertexGeneralLevelsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance scaledPlaneVertexGeneralLevelsNoetherian : IsNoetherian N :=
  extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
local instance scaledPlaneVertexGeneralLevelsTensorDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
noncomputable local instance scaledPlaneVertexGeneralLevelsAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable [Module.Finite (closedGaussParameterField H I) E]

include hvertex

/-- The original scaled-plane component constructs a point above the
vertex where every general level of the actual numerator/normal-power
quotient accumulates. Both local branches and all denominator poles are
proved from the original map and the exact scaled-power identity. -/
theorem scaled_plane_base_component_constructs_vertex_general_level_closure
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)
    (s n : Fin 4 → E) (hnlast : n (Fin.last 3) = 0)
    (hnvalue : aeval (extendedClosedGaussAffineTensorCoordinate H I E) ((O) n) ≠ 0)
    (a : E) (ha : a ≠ 0)
    (hpower : aeval (w) ((O) s) =
      algebraMap E (N).functionField (a ^ d) * (aeval (w) (L₀)) ^ d)
    (hbase : (O) s - C (a ^ d) * (L₀) ^ d ∈
      Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
        Set (MvPolynomial (Fin 4) E)))
    (Q : Ideal (MvPolynomial (Fin 4) K))
    (hQ : Q ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes) :
    s (Fin.last 3) ≠ 0 ∧ H (Fin.last 3) ∉ Q ∧
      ∃ x z : N, x ⤳ z ∧ (f) z = fourthAxisProjectivePoint E ∧
        ∃ hz : z ∈ V, ∃ S : Set E, S.Finite ∧ ∀ c : E, c ∉ S →
          IsLocalRing.closedPoint ((N).presheaf.stalk z) ∈
            closure (quotientLevelLocus ((N).presheaf.stalk z)
              (germ ((O) n) z hz) ((germ (L₀) z hz) ^ d)
              ((N).presheaf.germ ⊤ z (by trivial)
                (extendedClosedGaussGlobalConstantHom H I E hH e c))) := by
  obtain ⟨hs, hH4, b, j, hj, he, hNline, hLline, x, z, hxz, hx, hzimage⟩ :=
    scaled_plane_base_component_constructs_normalized_branch_through_vertex
      H I E hd hH hind hGauss hvertex e p q hq hrel hparameter s n hnlast a ha hbase Q hQ
  change (f) x = vertexLineProjectiveGenericPoint (fun i => (ι) (b i)) j
    ((_root_.map_ne_zero (ι)).mpr hj) at hx
  change (f) z = fourthAxisProjectivePoint E at hzimage
  have hz : z ∈ V := by
    rw [← extendedClosedGaussNormalizationProjectiveMap_preimage H I E hH e (Fin.last 3)]
    change X (Fin.last 3) ∉ ((f) z).asHomogeneousIdeal
    exact hzimage.symm ▸ fourthAxisProjectivePoint_fourth_coordinate_not_mem E
  have hxV : x ∈ V := hxz.mem_open (V).isOpen hz
  have hNhom := extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH n
  have hLhom := linearFormPolynomial_homogeneous
    (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)
  have hNx : germ ((O) n) x hxV ∈ IsLocalRing.maximalIdeal ((N).presheaf.stalk x) := by
    apply (native_polynomial_germ_mem_maximal_iff_projective_equation H I E hH e _ hNhom x _ hxV).mpr
    exact hx.symm ▸ hNline
  have hLx : IsUnit (germ (L₀) x hxV) := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro h
    have hp := (native_polynomial_germ_mem_maximal_iff_projective_equation
      H I E hH e _ hLhom x _ hxV).mp h
    have hp' : (L₀) ∈ (vertexLineProjectiveGenericPoint (fun i => (ι) (b i)) j
        ((_root_.map_ne_zero (ι)).mpr hj)).asHomogeneousIdeal := hx ▸ hp
    exact hLline hp'
  have hLz : germ (L₀) z hz ∈ IsLocalRing.maximalIdeal ((N).presheaf.stalk z) := by
    apply (native_polynomial_germ_mem_maximal_iff_projective_equation H I E hH e _ hLhom z _ hz).mpr
    have hb : b ≠ 0 := fun h => hj (congrFun h j)
    exact hzimage.symm ▸ (actual_normal_section_projective_vertex_line_values
      H I E hd hH hind hGauss hvertex e b hb j hj).1
  have hn0 : germ ((O) n) z hz ≠ 0 :=
    native_polynomial_germ_ne_zero_of_affine_source_value H I E hH e _ hNhom hnvalue z _ hz
  let φ : (N).presheaf.stalk z →+* (N).presheaf.stalk x := ((N).presheaf.stalkSpecializes hxz).hom
  have hmap (P : MvPolynomial (Fin 4) E) : φ (germ P z hz) = germ P x hxV :=
    native_polynomial_germ_stalkSpecializes H I E hH e P x z hxz _ hz
  letI : IsIntegrallyClosed ((N).presheaf.stalk z) :=
    extendedClosedGaussNormalizationScheme_stalk_isIntegrallyClosed H I E hH e z
  letI : Algebra E ((N).presheaf.stalk z) :=
    (((N).presheaf.germ ⊤ z (by trivial)).hom.comp
      (extendedClosedGaussGlobalConstantHom H I E hH e)).toAlgebra
  have hn : aeval (w) ((O) n) ≠ 0 := by
    intro hzero
    exact hn0 ((extendedClosedGaussPolynomialCoefficientGerm_eq_zero_iff H I E hH e ((O) n)
      (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH n) z _ hz).mpr hzero)
  have hL0 : aeval (w) (L₀) ≠ 0 := by
    intro hzero
    have hzeroz := (extendedClosedGaussPolynomialCoefficientGerm_eq_zero_iff H I E hH e (L₀)
      (linearFormPolynomial_homogeneous _) z _ hz).mpr hzero
    have hunit : IsUnit (0 : (N).presheaf.stalk x) := by
      have hh : IsUnit (φ (germ (L₀) z hz)) := by rw [hmap]; exact hLx
      simpa only [hzeroz, map_zero] using hh
    exact not_isUnit_zero hunit
  have hpoles (P : PrimeSpectrum ((N).presheaf.stalk z)) (hP : P.asIdeal.height = 1)
      (hlP : germ (L₀) z hz ∈ P.asIdeal) :
      algebraMap ((N).presheaf.stalk z) (N).functionField (germ ((O) n) z hz) /
          (algebraMap ((N).presheaf.stalk z) (N).functionField (germ (L₀) z hz)) ^ d ∉
        fractionPrimeLocalAlgebra ((N).presheaf.stalk z) P.asIdeal :=
    actual_stalk_denominator_height_one_prime_local_quotient_pole H I E hH e hd hind hGauss
      hvertex s n hs hnlast hn hL0 (a ^ d) hpower z (Fin.last 3) hz P hP hlP
  obtain ⟨S, hS, hlevels⟩ := local_zero_and_denominator_poles_construct_general_level_closure
    (k := E) ((N).presheaf.stalk z) φ (germ ((O) n) z hz) (germ (L₀) z hz) hn0
    (by rw [hmap]; exact hNx) (by rw [hmap]; exact hLx) hLz d hpoles
  exact ⟨hs, hH4, x, z, hxz, hzimage, hz, S, hS, hlevels⟩

end DimensionFourDependence
