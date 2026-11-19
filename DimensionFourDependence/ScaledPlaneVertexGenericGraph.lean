import DimensionFourDependence.ScaledPlaneNormalizedBaseBranch
import DimensionFourDependence.NativePolynomialGermPointEquations
import DimensionFourDependence.ProjectiveVertexLineNormalSection
import DimensionFourDependence.ScaledPlaneLocalHeightOneBranches
import DimensionFourDependence.ActualVertexStalkDenominatorPoles
import DimensionFourDependence.NormalGraphResidueKernel
import DimensionFourDependence.NormalBranchGeneralLevelClosure
import DimensionFourDependence.LocalZeroPoleCriterion

/-! # The actual scaled-plane vertex constructs a free generic graph parameter -/

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

local instance scaledPlaneVertexGenericGraphIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance scaledPlaneVertexGenericGraphNoetherian : IsNoetherian N :=
  extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
local instance scaledPlaneVertexGenericGraphTensorDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
noncomputable local instance scaledPlaneVertexGenericGraphAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable [Module.Finite (closedGaussParameterField H I) E]

include hvertex

/-- The original scaled-plane base component constructs a normalized
point above the vertex where the actual quotient's entire graph kernel
vanishes coefficientwise. Consequently its graph residue parameter is
free; no specialization of a generic target coordinate is used. -/
theorem scaled_plane_base_component_constructs_free_generic_graph_at_vertex
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
        z ∈ V ∧ aeval (w) (L₀) ≠ 0 ∧
        RingHom.ker (Polynomial.aeval (aeval (w) ((O) n) / (aeval (w) (L₀)) ^ d) :
          Polynomial ((N).presheaf.stalk z) →ₐ[(N).presheaf.stalk z] (N).functionField).toRingHom ≤
          RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue ((N).presheaf.stalk z))) := by
  obtain ⟨hs, hH4, x, z, hxz, hzimage, hz, q₀, qL, hq₀, hqL, hne, hnq₀, hlq₀, hlqL, g₀, hg₀, hgm₀⟩ :=
    scaled_plane_base_component_constructs_local_height_one_branches H I E hd hH hind hGauss
      hvertex e p q hq hrel hparameter s n hnlast hnvalue a ha hbase Q hQ
  let R := (N).presheaf.stalk z
  letI : IsIntegrallyClosed R :=
    extendedClosedGaussNormalizationScheme_stalk_isIntegrallyClosed H I E hH e z
  letI : Algebra E R := (((N).presheaf.germ ⊤ z (by trivial)).hom.comp
    (extendedClosedGaussGlobalConstantHom H I E hH e)).toAlgebra
  letI : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap C₀ E).injective
  let Fq : (N).functionField := aeval (w) ((O) n) / (aeval (w) (L₀)) ^ d
  have hn : aeval (w) ((O) n) ≠ 0 := by
    intro he
    exact hnvalue ((extendedClosedGauss_affine_tensor_native_homogeneous_zero_iff
      H I E hH e ((O) n) (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH n)).mpr he)
  have hL : aeval (w) (L₀) ≠ 0 := by
    intro he
    have he' := (extendedClosedGaussPolynomialCoefficientGerm_eq_zero_iff H I E hH e (L₀)
      (linearFormPolynomial_homogeneous _) z (Fin.last 3) hz).mpr he
    exact hlq₀ (he' ▸ q₀.asIdeal.zero_mem)
  have hFq : Fq ≠ 0 := div_ne_zero hn (pow_ne_zero d hL)
  have hpole : Fq ∉ fractionPrimeLocalAlgebra R qL.asIdeal :=
    actual_stalk_denominator_height_one_prime_scaled_quotient_pole H I E hH e hd hind hGauss
      hvertex s n hs hnlast hn hL (a ^ d) hpower z (Fin.last 3) hz qL hqL hlqL
  obtain ⟨gL, hgL, hgmL⟩ := normal_height_one_nonregular_constructs_inverse_zero_germ
    R qL.asIdeal hqL Fq hpole
  let V₀ := normalHeightOneValuationSubring (F := (N).functionField) R q₀.asIdeal hq₀
  let Vinf := normalHeightOneValuationSubring (F := (N).functionField) R qL.asIdeal hqL
  have hzero : Fq ∈ V₀.nonunits := by
    have hg := normal_branch_vanishing_mem_valuation_nonunits R q₀.asIdeal hq₀ g₀ hgm₀
    rw [hg₀] at hg
    exact hg
  have hpinv : Fq⁻¹ ∈ Vinf.nonunits := hgL ▸
    normal_branch_vanishing_mem_valuation_nonunits R qL.asIdeal hqL gL hgmL
  refine ⟨hs, hH4, x, z, hxz, hzimage, hz, hL, ?_⟩
  exact zero_pole_graph_kernel_le_residue_polynomial_kernel (k := E) Fq V₀ Vinf
    (fun r => (fractionPrimeLocalAlgebra R q₀.asIdeal).algebraMap_mem r)
    (fun r => (fractionPrimeLocalAlgebra R qL.asIdeal).algebraMap_mem r) hzero hpinv hFq

end DimensionFourDependence

