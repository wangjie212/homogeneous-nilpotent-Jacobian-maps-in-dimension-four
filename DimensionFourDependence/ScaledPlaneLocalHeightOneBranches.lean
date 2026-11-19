import DimensionFourDependence.ScaledPlaneNormalizedBaseBranch
import DimensionFourDependence.NativePolynomialGermPointEquations
import DimensionFourDependence.ProjectiveVertexLineNormalSection
import DimensionFourDependence.SeparatingZeroDivisors

/-! # Height-one branches in the actual normalized vertex stalk

The original scaled-plane data construct both normalization points. Their
actual specialization map then constructs distinct height-one zero and
denominator branches in the same vertex stalk. The first carries the exact
original quotient as a vanishing germ. Denominator poles remain to prove.
-/

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

/-- Equal homogeneous degrees cancel the chosen local frame in
the actual numerator-over-normal-power quotient. -/
theorem homogeneous_frame_quotient_cancel
    {F : Type*} [Field F] (n l u : F) (hu : u ≠ 0) (d : ℕ) :
    (n / u ^ d) / (l / u) ^ d = n / l ^ d := by
  rw [div_pow]
  field_simp [hu]

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

local instance scaledPlaneLocalHeightOneBranchesIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance scaledPlaneLocalHeightOneBranchesNoetherian : IsNoetherian N :=
  extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
local instance scaledPlaneLocalHeightOneBranchesTensorDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
noncomputable local instance scaledPlaneLocalHeightOneBranchesAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

include hvertex

/-- Every original scaled-plane base component and its nonzero
actual numerator construct distinct height-one branches in an actual
normalized vertex stalk, with the original quotient vanishing on the
first branch and the normal denominator vanishing on the second. -/
theorem scaled_plane_base_component_constructs_local_height_one_branches
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)
    (s n : Fin 4 → E) (hnlast : n (Fin.last 3) = 0)
    (hnvalue : aeval (extendedClosedGaussAffineTensorCoordinate H I E) ((O) n) ≠ 0)
    (a : E) (ha : a ≠ 0)
    (hbase : (O) s - C (a ^ d) * (L₀) ^ d ∈
      Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
        Set (MvPolynomial (Fin 4) E)))
    (Q : Ideal (MvPolynomial (Fin 4) K))
    (hQ : Q ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes) :
    s (Fin.last 3) ≠ 0 ∧ H (Fin.last 3) ∉ Q ∧
      ∃ x z : N, x ⤳ z ∧ (f) z = fourthAxisProjectivePoint E ∧
        ∃ hz : z ∈ V, ∃ q₀ qL : PrimeSpectrum ((N).presheaf.stalk z),
          q₀.asIdeal.height = 1 ∧ qL.asIdeal.height = 1 ∧ q₀ ≠ qL ∧
          germ ((O) n) z hz ∈ q₀.asIdeal ∧ germ (L₀) z hz ∉ q₀.asIdeal ∧
          germ (L₀) z hz ∈ qL.asIdeal ∧
          ∃ g : fractionPrimeLocalAlgebra (F := (N).functionField) ((N).presheaf.stalk z) q₀.asIdeal,
            (g : (N).functionField) = aeval (w) ((O) n) / (aeval (w) (L₀)) ^ d ∧
            g ∈ IsLocalRing.maximalIdeal
              (fractionPrimeLocalAlgebra (F := (N).functionField) ((N).presheaf.stalk z) q₀.asIdeal) := by
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
  obtain ⟨q₀, qL, hq₀, hqL, hne, hnq₀, hlq₀, hlqL, g, hg, hgmem⟩ :=
    local_map_constructs_distinct_zero_and_denominator_divisors
      (F := (N).functionField) φ (germ ((O) n) z hz) (germ (L₀) z hz) hn0
      (by rw [hmap]; exact hNx) (by rw [hmap]; exact hLx) hLz d
  refine ⟨hs, hH4, x, z, hxz, hzimage, hz, q₀, qL, hq₀, hqL, hne, hnq₀, hlq₀, hlqL, g, ?_, hgmem⟩
  rw [hg, extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e _ hNhom,
    extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e _ hLhom]
  simpa only [pow_one] using homogeneous_frame_quotient_cancel
    (aeval (w) ((O) n)) (aeval (w) (L₀)) ((w) (Fin.last 3))
    (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e _) d

end DimensionFourDependence
