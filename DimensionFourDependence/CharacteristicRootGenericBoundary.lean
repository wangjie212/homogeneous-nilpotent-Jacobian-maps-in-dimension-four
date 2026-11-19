import DimensionFourDependence.CharacteristicRootGenericGraph
import DimensionFourDependence.GenericGraphProjectiveBoundary

/-! # The actual root-divisor intersection lies at infinity over the unspecialized pencil field -/

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
  (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "C₀" => closedGaussParameterField H I
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH
  (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss 0
local notation "Lₜ" => ∑ j, algebraMap E (N).functionField ((ν₀) j) * (w) j
local notation "L₀" => extendedClosedGaussInputLinearSection H I E hH e (ν₀)
local notation "t₀" r:max => nativeCharacteristicPencilValue H I E hH e
  (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r
local notation "Z₀" z:max b:max hb:max => fun j : Option (Fin 4) =>
  j.elim ((N).presheaf.germ (U b) z hb
    (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (L₀) b))
      (nativeProjectiveCoordinateGerm H I E hH e z b hb)

local instance characteristicRootGenericBoundaryIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicRootGenericBoundaryAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The boundary is the residue of the same original projective
coordinate germs. Its level parameter stays free in both fields, and
its affine homogenizing coordinate vanishes. -/
noncomputable def NativeCharacteristicPencilGenericBoundaryAtPoint
    (r : (N).functionField) (z : N) (b : Fin 4) (hb : z ∈ U b) : Prop :=
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
  ∃ α : RatFunc E →ₐ[E] (N).functionField, α RatFunc.X = (t₀ r) ∧
    letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
    ∃ β : RatFunc E →+* RatFunc (IsLocalRing.ResidueField ((N).presheaf.stalk z)),
      β RatFunc.X = RatFunc.X ∧
      letI : Algebra (RatFunc E) (RatFunc (IsLocalRing.ResidueField ((N).presheaf.stalk z))) := β.toAlgebra
      ∃ hξ : (fun j => RatFunc.C (IsLocalRing.residue ((N).presheaf.stalk z) ((Z₀ z b hb) j))) ≠ 0,
        projectiveFieldPoint (E := RatFunc E)
          (fun j => RatFunc.C (IsLocalRing.residue ((N).presheaf.stalk z) ((Z₀ z b hb) j))) hξ ∈
            projectiveClosureSet (L := RatFunc E) (fun i => (w) i / (Lₜ)) ∧
        RatFunc.C (IsLocalRing.residue ((N).presheaf.stalk z) ((Z₀ z b hb) none)) = 0

/-- The free actual graph and the actual vanishing hyperplane germ
construct the same-point boundary over the unspecialized level field.
No boundary direction, scalar level or coefficient-field embedding is supplied. -/
theorem native_free_characteristic_graph_constructs_generic_level_boundary
    (r : (N).functionField) (z : N) (b : Fin 4) (hb : z ∈ U b)
    (hker : RingHom.ker (Polynomial.aeval (t₀ r) :
      Polynomial ((N).presheaf.stalk z) →ₐ[(N).presheaf.stalk z] (N).functionField).toRingHom ≤
        RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue ((N).presheaf.stalk z))))
    (hLz : (N).presheaf.germ (U b) z hb
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (L₀) b) ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk z)) :
    NativeCharacteristicPencilGenericBoundaryAtPoint H I E hH e hd hind hGauss r z b hb := by
  let R := (N).presheaf.stalk z
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
  letI := extendedClosedGaussStalkCoefficientAlgebra_scalarTower H I E hH e z
  have ht := rationalGraph_parameter_transcendental (k := E) (t₀ r) hker
  have ht0 : (t₀ r) ≠ 0 := by
    intro he
    apply ht
    rw [he]
    exact isAlgebraic_zero
  have hL0 : (Lₜ) ≠ 0 := by
    intro he
    apply ht0
    change r / (Lₜ) = 0
    rw [he, div_zero]
  let Z := Z₀ z b hb
  have hcoords (j : Option (Fin 4)) : algebraMap R (N).functionField (Z j) =
      ((Lₜ) / (w) b) * j.elim 1 (fun i => (w) i / (Lₜ)) := by
    cases j with
    | none =>
      change algebraMap R (N).functionField
        ((N).presheaf.germ (U b) z hb
          (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (L₀) b)) = ((Lₜ) / (w) b) * 1
      rw [extendedClosedGaussHyperplaneGlobalCoefficient_germ_value,
        extendedClosedGaussInputLinearSection_value, mul_one]
    | some i =>
      change algebraMap R (N).functionField
        (nativeProjectiveCoordinateGerm H I E hH e z b hb i) = ((Lₜ) / (w) b) * ((w) i / (Lₜ))
      rw [nativeProjectiveCoordinateGerm_value]
      field_simp [hL0, extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e b]
  have hres : (fun j => IsLocalRing.residue R (Z j)) ≠ 0 := by
    intro he
    have hz := congrFun he (some b)
    change IsLocalRing.residue R (nativeProjectiveCoordinateGerm H I E hH e z b hb b) = 0 at hz
    rw [nativeProjectiveCoordinateGerm_frame, map_one] at hz
    exact one_ne_zero hz
  obtain ⟨α, hα, β, hβ, hξ, hpoint⟩ := rational_graph_constructs_generic_level_projective_boundary
    (k := E) (t₀ r) hker (fun i => (w) i / (Lₜ)) ((Lₜ) / (w) b) Z hcoords hres
  refine ⟨α, hα, β, hβ, hξ, hpoint, ?_⟩
  have hz : IsLocalRing.residue R (Z none) = 0 := (IsLocalRing.residue_eq_zero_iff (Z none)).mpr hLz
  exact (congrArg RatFunc.C hz).trans (map_zero RatFunc.C)

variable [Module.Finite (closedGaussParameterField H I) E]

local notation "T₀" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "z₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q
local notation "ha₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q
local notation "ρ₀" c:max r:max hroot:max => extendedClosedGaussOutputLinearRootSection H I E hH e
  c r (Nat.lt_trans Nat.zero_lt_one hd) hroot

/-- Every actual root-zero divisor constructs a boundary at infinity
of the actual generic pencil curve, on a proper specialization of its
own branch and with the original coordinate germs retained. -/
theorem actual_characteristic_root_divisor_constructs_generic_level_boundary
    (cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval (w) ((O) cS))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss cN r)
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (hzero : (N).presheaf.germ (U a) (z₀ a q) (ha₀ a q)
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (ρ₀ cS r hroot) a) ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk (z₀ a q))) :
    ∃ z : N, (z₀ a q) ⤳ z ∧ (z₀ a q) ≠ z ∧ ∃ (b : Fin 4) (hb : z ∈ U b),
      NativeCharacteristicPencilGenericBoundaryAtPoint H I E hH e hd hind hGauss r z b hb := by
  obtain ⟨z, hxz, hne, b, hb, _hρz, hLz, hker⟩ :=
    actual_characteristic_root_divisor_constructs_free_generic_graph
      H I E hH e hd hind hGauss cS cN r hr hroot hfactor a q hq hzero
  exact ⟨z, hxz, hne, b, hb, native_free_characteristic_graph_constructs_generic_level_boundary
    H I E hH e hd hind hGauss r z b hb hker hLz⟩

end DimensionFourDependence
