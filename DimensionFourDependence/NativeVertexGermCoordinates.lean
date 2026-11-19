import DimensionFourDependence.NativePolynomialGermPointEquations
import DimensionFourDependence.ProjectiveVertexLineNormalSection

/-! # Actual regular homogeneous coordinates at the fixed source vertex -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "V" => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' (Fin.last 3))
local notation "f" => extendedClosedGaussNormalizationProjectiveMap H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "germ" P:max z:max hz:max =>
  extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z (Fin.last 3) hz

local instance nativeVertexGermCoordinatesIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeVertexGermCoordinatesAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The frame coordinate is the actual unit germ, rather than only
a unit up to an unspecified projective rescaling. -/
theorem native_vertex_frame_germ_eq_one (z : N) (hz : z ∈ V) :
    germ (X (Fin.last 3)) z hz = 1 := by
  apply IsFractionRing.injective ((N).presheaf.stalk z) (N).functionField
  rw [extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e _ (isHomogeneous_X _ _),
    aeval_X, pow_one, div_self
      (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e _), map_one]

/-- Every original coordinate germ has exactly the expected residue
at the fixed vertex, including its normalized last coordinate. -/
theorem native_vertex_coordinate_germ_residue
    (z : N) (hz : z ∈ V) (himage : (f) z = fourthAxisProjectivePoint E) (i : Fin 4) :
    IsLocalRing.residue ((N).presheaf.stalk z) (germ (X i) z hz) =
      (Fin.snoc (0 : Fin 3 → IsLocalRing.ResidueField ((N).presheaf.stalk z)) 1 :
        Fin 4 → IsLocalRing.ResidueField ((N).presheaf.stalk z)) i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [native_vertex_frame_germ_eq_one, map_one, Fin.snoc_last]
  · rw [Fin.snoc_castSucc, Pi.zero_apply, IsLocalRing.residue_eq_zero_iff]
    apply (native_polynomial_germ_mem_maximal_iff_projective_equation H I E hH e
      (X j.castSucc) (isHomogeneous_X _ _) z (Fin.last 3) hz).mpr
    rw [himage]
    apply (projectiveCoordinatePoint_mem_homogeneous _ _ (isHomogeneous_X _ _)).mpr
    simp only [aeval_X, Fin.snoc_castSucc, Pi.zero_apply]

/-- A homogeneous equation of the actual vertex vanishes after
reducing its actual native regular germ. -/
theorem native_vertex_form_germ_residue_zero
    (P : MvPolynomial (Fin 4) E) {D : ℕ} (hP : P.IsHomogeneous D)
    (hPvertex : P ∈ (fourthAxisProjectivePoint E).asHomogeneousIdeal)
    (z : N) (hz : z ∈ V) (himage : (f) z = fourthAxisProjectivePoint E) :
    IsLocalRing.residue ((N).presheaf.stalk z) (germ P z hz) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  apply (native_polynomial_germ_mem_maximal_iff_projective_equation H I E hH e P hP z
    (Fin.last 3) hz).mpr
  rwa [himage]

/-- The original L-normalized affine coordinates admit actual regular
projective coordinates whose residues are the fixed vertex at infinity. -/
theorem native_vertex_affine_projective_germ_coordinates
    (L : MvPolynomial (Fin 4) E) (hL : L.IsHomogeneous 1)
    (hLvertex : L ∈ (fourthAxisProjectivePoint E).asHomogeneousIdeal)
    (hLvalue : aeval (w) L ≠ 0)
    (z : N) (hz : z ∈ V) (himage : (f) z = fourthAxisProjectivePoint E) :
    let zR : Option (Fin 4) → (N).presheaf.stalk z :=
      fun j => j.elim (germ L z hz) (fun i => germ (X i) z hz)
    (∀ j, algebraMap ((N).presheaf.stalk z) (N).functionField (zR j) =
      (aeval (w) L / (w) (Fin.last 3)) *
        j.elim 1 (fun i => (w) i / aeval (w) L)) ∧
    (fun j => IsLocalRing.residue ((N).presheaf.stalk z) (zR j)) =
      (fun j : Option (Fin 4) => j.elim 0
        (Fin.snoc (0 : Fin 3 → IsLocalRing.ResidueField ((N).presheaf.stalk z)) 1)) := by
  refine ⟨?_, ?_⟩
  · intro j
    cases j with
    | none =>
      simpa only [Option.elim_none, pow_one, mul_one] using
        extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e L hL z (Fin.last 3) hz
    | some i =>
      simp only [Option.elim_some]
      rw [extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e _ (isHomogeneous_X _ _),
        aeval_X, pow_one]
      field_simp
  · funext j
    cases j with
    | none => exact native_vertex_form_germ_residue_zero H I E hH e L hL hLvertex z hz himage
    | some i => exact native_vertex_coordinate_germ_residue H I E hH e z hz himage i

end DimensionFourDependence
