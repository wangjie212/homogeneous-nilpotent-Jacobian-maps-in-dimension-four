import DimensionFourDependence.CharacteristicRootScaledBoundary
import DimensionFourDependence.NativeCharacteristicFullOutputEmbedding
import DimensionFourDependence.AlgebraicCompatibleSourceComponent
import DimensionFourDependence.CompatibleExtensionBoundaryTransport

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

local instance characteristicRootOriginalBoundaryIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicRootOriginalBoundaryAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

noncomputable local instance characteristicRootOriginalBoundaryOriginalAlgebra : Algebra K (N).functionField :=
  extendedClosedGaussOriginalSourceAlgebra H I E hH e

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "D₀" => polynomialOutputField H
local notation "Cᵣ" => RatFunc (RatFunc E)
local notation "Gᵣ" => RatFunc (N).functionField
local notation "κ₀" z:max => IsLocalRing.ResidueField ((N).presheaf.stalk z)
local notation "B₀" z:max => RatFunc (RatFunc (κ₀ z))
local notation "ξ₀" z:max b:max hb:max => fun j => RatFunc.C (RatFunc.C
  (IsLocalRing.residue ((N).presheaf.stalk z) ((Z₀ z b hb) j)))
local notation "vᵣ" => fun i => RatFunc.X * RatFunc.C ((w) i / (Lₜ))
local notation "Φ₀" hT:max => nativeCharacteristicScaleSourceHom H I E hH e
  (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss hT

/-- The original-coordinate intersection is a boundary of an actual
component of the original full generic fiber. The entire output-field
embedding is algebraic, and both free parameters and every original
coefficient retain their specified values on the boundary side. -/
noncomputable def NativeCharacteristicOriginalFiberBoundaryAtPoint
    (r : (N).functionField) (z : N) (b : Fin 4) (hb : z ∈ U b) : Prop :=
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
  ∃ (hT : (Lₜ) ≠ 0) (α : RatFunc E →ₐ[E] (N).functionField),
    α RatFunc.X = (t₀ r) ∧
    letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
    ∃ γ : Cᵣ →ₐ[RatFunc E] Gᵣ, γ RatFunc.X = RatFunc.X ∧
      ∃ ε : D₀ →+* Cᵣ,
        (∀ c : K, ε (algebraMap K D₀ c) = RatFunc.C (RatFunc.C
          (extendedClosedGaussSourceCoefficientHom H I E c))) ∧
        (∀ q : D₀, γ (ε q) = (Φ₀ hT) (q : S₀)) ∧
        (letI : Algebra D₀ Cᵣ := ε.toAlgebra; Algebra.IsAlgebraic D₀ Cᵣ) ∧
        (letI : Algebra D₀ Cᵣ := ε.toAlgebra;
          letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra;
          fiberVanishingIdeal (L := Cᵣ) (vᵣ) ∈
            (extendCoefficientIdeal Cᵣ (fiberVanishingIdeal (L := D₀)
              (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) ∧
        ∃ η : Cᵣ →+* B₀ z, η RatFunc.X = RatFunc.X ∧
          η (RatFunc.C (RatFunc.X : RatFunc E)) =
            RatFunc.C (RatFunc.X : RatFunc (κ₀ z)) ∧
          (∀ c : E, η (RatFunc.C (RatFunc.C c)) = RatFunc.C (RatFunc.C
            (IsLocalRing.residue ((N).presheaf.stalk z) (algebraMap E ((N).presheaf.stalk z) c)))) ∧
          letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra
          letI : Algebra Cᵣ (B₀ z) := η.toAlgebra
          ∃ hξ : (ξ₀ z b hb) ≠ 0,
            projectiveFieldPoint (E := Cᵣ) (ξ₀ z b hb) hξ ∈
                projectiveClosureSet (L := Cᵣ) (vᵣ) ∧
            (letI : Algebra D₀ (B₀ z) := (η.comp ε).toAlgebra;
              projectiveFieldPoint (E := D₀) (ξ₀ z b hb) hξ ∈
                projectiveClosureSet (L := D₀) (rationalCoordinate (K := K) (n := 4))) ∧
            (ξ₀ z b hb) none = 0

/-- The actual characteristic factorization identifies the constructed
scaled boundary with the original full generic fiber, preserving the
same original coordinate residues at the same intersection point. -/
theorem native_characteristic_scaled_boundary_constructs_original_full_output_boundary
    (cN : Fin 4 → E) (r : (N).functionField)
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss cN r)
    (z : N) (b : Fin 4) (hb : z ∈ U b)
    (hboundary : NativeCharacteristicPencilScaledBoundaryAtPoint H I E hH e hd hind hGauss r z b hb) :
    NativeCharacteristicOriginalFiberBoundaryAtPoint H I E hH e hd hind hGauss r z b hb := by
  let R := (N).presheaf.stalk z
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
  obtain ⟨α, hα, β, hβ, γ, hγ, δ, hδ, hξ, hpoint, hzero⟩ := hboundary
  have ht0 : (t₀ r) ≠ 0 := by
    rw [← hα]
    exact (map_ne_zero α).mpr RatFunc.X_ne_zero
  have hT : (Lₜ) ≠ 0 := by
    intro he
    apply ht0
    change r / (Lₜ) = 0
    rw [he, div_zero]
  letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
  letI : Algebra (RatFunc E) (RatFunc (κ₀ z)) := β.toRingHom.toAlgebra
  letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra
  letI : Algebra Cᵣ (B₀ z) := δ.toRingHom.toAlgebra
  obtain ⟨V, W, hVW, _hV, _hW, _hchar, _hspan, _hN, hY⟩ := hfactor
  obtain ⟨ε, hεK, _hεY, hcompat, halg⟩ :=
    native_characteristic_scaled_factorization_constructs_algebraic_full_output_embedding
      H I E (Nat.lt_trans Nat.zero_lt_one hd) hH e hind hGauss r V W hVW hY hT α hα γ hγ
  have hcoords (i : Fin 4) : (Φ₀ hT) (rationalCoordinate (K := K) i) = (vᵣ) i :=
    nativeCharacteristicScaleSourceHom_coordinate H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss hT i
  have hcomponent := original_full_output_compatible_source_constructs_actual_component H
    ε γ.toRingHom (Φ₀ hT).toRingHom hcompat (vᵣ) hcoords halg
  refine ⟨hT, α, hα, γ, hγ, ε, hεK, hcompat, halg, hcomponent,
    δ.toRingHom, hδ, ?_, ?_, hξ, hpoint, ?_, hzero⟩
  · change δ (RatFunc.C (RatFunc.X : RatFunc E)) =
      RatFunc.C (RatFunc.X : RatFunc (κ₀ z))
    exact (δ.commutes RatFunc.X).trans
      ((IsScalarTower.algebraMap_apply (RatFunc E) (RatFunc (κ₀ z)) (B₀ z) RatFunc.X).trans
        (congrArg RatFunc.C hβ))
  · intro c
    change δ (RatFunc.C (RatFunc.C c)) = _
    calc
      δ (RatFunc.C (RatFunc.C c)) = RatFunc.C (β (RatFunc.C c)) :=
        (δ.commutes (RatFunc.C c)).trans
          (IsScalarTower.algebraMap_apply (RatFunc E) (RatFunc (κ₀ z)) (B₀ z) (RatFunc.C c))
      _ = _ := congrArg RatFunc.C (β.commutes c)
  · exact compatible_source_extension_boundary_mem_original_coefficient_closure
      (Φ₀ hT).toRingHom ε (rationalCoordinate (K := K) (n := 4)) (vᵣ)
      (fun q => (hcompat q).symm) hcoords (ξ₀ z b hb) hξ hpoint

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
theorem actual_characteristic_root_divisor_constructs_original_full_output_boundary
    (cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval (w) ((O) cS))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss cN r)
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (hzero : (N).presheaf.germ (U a) (z₀ a q) (ha₀ a q)
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (ρ₀ cS r hroot) a) ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk (z₀ a q))) :
    ∃ z : N, (z₀ a q) ⤳ z ∧ (z₀ a q) ≠ z ∧ ∃ (b : Fin 4) (hb : z ∈ U b),
      NativeCharacteristicOriginalFiberBoundaryAtPoint H I E hH e hd hind hGauss r z b hb := by
  obtain ⟨z, hxz, hne, b, hb, hboundary⟩ :=
    actual_characteristic_root_divisor_constructs_scaled_generic_boundary
      H I E hH e hd hind hGauss cS cN r hr hroot hfactor a q hq hzero
  exact ⟨z, hxz, hne, b, hb,
    native_characteristic_scaled_boundary_constructs_original_full_output_boundary
      H I E hH e hd hind hGauss cN r hfactor z b hb hboundary⟩

end DimensionFourDependence
