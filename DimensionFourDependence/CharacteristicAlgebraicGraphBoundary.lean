import DimensionFourDependence.NativeRelativeGraphCoefficients
import DimensionFourDependence.CharacteristicRootOriginalBoundary
import DimensionFourDependence.NormalizedProjectivePointLift
import DimensionFourDependence.CompatibleAlgebraicGraphBoundaryLift

/-! # The same characteristic-root boundary has an algebraic original graph realization -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E
local notation "D₀" => polynomialOutputField H
local notation "L" => coefficientField (K := K)
  (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc)))
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "Cᵣ" => RatFunc (RatFunc E)
local notation "Gᵣ" => RatFunc (N).functionField

local instance characteristicAlgebraicGraphBoundaryDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
local instance characteristicAlgebraicGraphBoundaryIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicAlgebraicGraphBoundaryExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

noncomputable local instance characteristicAlgebraicGraphBoundaryOriginalAlgebra : Algebra K (N).functionField :=
  extendedClosedGaussOriginalSourceAlgebra H I E hH e

noncomputable local instance characteristicAlgebraicGraphBoundaryExtendedSMul : SMul E (N).functionField :=
  (extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e).toSMul
noncomputable local instance characteristicAlgebraicGraphBoundaryOriginalSMul : SMul K (N).functionField :=
  (extendedClosedGaussOriginalSourceAlgebra H I E hH e).toSMul

variable (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "U" b:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' b)
local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH
  (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss 0
local notation "Lₜ" => ∑ j, algebraMap E (N).functionField ((ν₀) j) * (w) j
local notation "L₀" => linearFormPolynomial (ν₀)
local notation "vᵣ" => fun i => RatFunc.X * RatFunc.C ((w) i / (Lₜ))
local notation "Jᵣ" => algebraicClosure Cᵣ Gᵣ
local notation "Φ₀" hT:max => nativeCharacteristicScaleSourceHom H I E hH e
  (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss hT
local notation "Z₀" z:max b:max hb:max => fun j : Option (Fin 4) =>
  j.elim ((N).presheaf.germ (U b) z hb
    (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
      (extendedClosedGaussInputLinearSection H I E hH e (ν₀)) b))
        (nativeProjectiveCoordinateGerm H I E hH e z b hb)
local notation "ξ₀" z:max b:max hb:max => fun j => RatFunc.C (RatFunc.C
  (IsLocalRing.residue ((N).presheaf.stalk z) ((Z₀ z b hb) j)))

include hrank

/-- The same native intersection lifts to the actual relative constants
of its original source realization. Its normalized coordinate field is
algebraic over the original graph coefficients, its frame is the same
original source-coordinate label, and its entire original boundary prime
is retained by coefficient contraction. -/
theorem actual_characteristic_original_boundary_constructs_algebraic_graph_boundary
    (hN : IsNilpotent (jac H))
    (c qinv : L)
    (hc : (c : S₀) = firstFiberInvariantInChart p
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))) hY h)
    (hqinv : (qinv : S₀) = secondFiberInvariant p
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))) hY h c)
    (r : (N).functionField) (z : N) (b : Fin 4) (hb : z ∈ U b)
    (hboundary : NativeCharacteristicOriginalFiberBoundaryAtPoint H I E hH e hd hind hGauss r z b hb) :
    letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
    ∃ (hT : (Lₜ) ≠ 0) (α : RatFunc E →ₐ[E] (N).functionField),
      α RatFunc.X = nativeCharacteristicPencilValue H I E hH e
        (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r ∧
      letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
      ∃ γ : Cᵣ →ₐ[RatFunc E] Gᵣ, γ RatFunc.X = RatFunc.X ∧
        letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra
        ∃ η : Cᵣ →+* RatFunc (RatFunc (IsLocalRing.ResidueField ((N).presheaf.stalk z))),
          η RatFunc.X = RatFunc.X ∧
          η (RatFunc.C (RatFunc.X : RatFunc E)) =
            RatFunc.C (RatFunc.X : RatFunc (IsLocalRing.ResidueField ((N).presheaf.stalk z))) ∧
          (∀ t : E, η (RatFunc.C (RatFunc.C t)) = RatFunc.C (RatFunc.C
            (IsLocalRing.residue ((N).presheaf.stalk z) (algebraMap E ((N).presheaf.stalk z) t)))) ∧
          letI : Algebra Cᵣ (RatFunc (RatFunc (IsLocalRing.ResidueField ((N).presheaf.stalk z)))) := η.toAlgebra
          ∃ g : (L) →+* Jᵣ,
            (∀ l : L, algebraMap Jᵣ Gᵣ (g l) = (Φ₀ hT) (l : S₀)) ∧
            (∀ k : K, g (algebraMap K (L) k) = algebraMap Cᵣ Jᵣ (RatFunc.C (RatFunc.C ((ι) k)))) ∧
            (∀ t : C₀, g ((a) t) = algebraMap Cᵣ Jᵣ (RatFunc.C (RatFunc.C (algebraMap C₀ E t)))) ∧
            letI : Algebra (L) Jᵣ := g.toAlgebra
            letI : SMul (L) Jᵣ := g.toAlgebra.toSMul
            Algebra.IsAlgebraic (L) Jᵣ ∧
            ∃ (F : Type u) (hF : Field F),
              letI : Field F := hF
              ∃ aJF : Algebra Jᵣ F,
                letI : Algebra Jᵣ F := aJF
                letI : SMul Jᵣ F := aJF.toSMul
                ∃ (ξ : Option (Fin 4) → F) (hξ : ξ ≠ 0),
                  (letI : Algebra Cᵣ F := ((algebraMap Jᵣ F).comp (algebraMap Cᵣ Jᵣ)).toAlgebra;
                    (projectiveFieldPointIdeal (E := Cᵣ) ξ).toIdeal =
                      (projectiveFieldPointIdeal (E := Cᵣ) (ξ₀ z b hb)).toIdeal) ∧
                  letI : Algebra (L) F := ((algebraMap Jᵣ F).comp g).toAlgebra
                  letI : SMul (L) F := (((algebraMap Jᵣ F).comp g).toAlgebra).toSMul
                  Algebra.IsAlgebraic (L) F ∧
                  projectiveFieldPoint (E := L) ξ hξ ∈
                    projectiveClosureSet («L» := L) (rationalCoordinate (K := K) (n := 4)) ∧
                  ξ none = 0 ∧ ξ (some b) = 1 := by
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
  obtain ⟨hT, α, hα, γ, hγ, ε, hεK, hcompat, halg, _hcomponent,
    η, hηX, hηlevel, hηE, hξ, hpoint, _hpointD, hzero⟩ := hboundary
  letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
  letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra
  letI : SMul Cᵣ Gᵣ := γ.toRingHom.toAlgebra.toSMul
  letI : Algebra Jᵣ Gᵣ := (Jᵣ).val.toRingHom.toAlgebra
  letI : SMul Jᵣ Gᵣ := (Jᵣ).val.toRingHom.toAlgebra.toSMul
  letI : IsScalarTower Cᵣ Jᵣ Gᵣ := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra Cᵣ (RatFunc (RatFunc (IsLocalRing.ResidueField ((N).presheaf.stalk z)))) := η.toAlgebra
  have hL : aeval (R := E) (w) (L₀) ≠ 0 := by
    simpa only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X] using hT
  obtain ⟨g, hg, hgK, hgC, _hgD, hJalg⟩ :=
    native_scaled_source_constructs_same_relative_graph_coefficients
      H hrank I p hY h hh E hH e (L₀) hL α γ ε hεK hcompat halg
  let p₀ := projectiveFieldPoint (E := Cᵣ) (ξ₀ z b hb) hξ
  have hp0 : X none ∈ p₀.asHomogeneousIdeal := by
    apply (projectiveFieldPointIdeal_mem_homogeneous (K := Cᵣ) (ξ₀ z b hb) (X none)
      (isHomogeneous_X (R := Cᵣ) none)).mpr
    rw [aeval_X]
    exact hzero
  have hframe : (ξ₀ z b hb) (some b) = 1 := by
    change RatFunc.C (RatFunc.C (IsLocalRing.residue ((N).presheaf.stalk z)
      (nativeProjectiveCoordinateGerm H I E hH e z b hb b))) = 1
    rw [nativeProjectiveCoordinateGerm_frame, map_one, map_one, map_one]
  have hpb : X (some b) ∉ p₀.asHomogeneousIdeal :=
    projectiveFieldPointIdeal_X_not_mem_of_coordinate_eq_one (E := Cᵣ) (ξ₀ z b hb) (some b) hframe
  have hcoords (i : Fin 4) : (Φ₀ hT) (rationalCoordinate (K := K) i) = (vᵣ) i :=
    nativeCharacteristicScaleSourceHom_coordinate H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss hT i
  obtain ⟨Q, hQb, hQideal, hRalg, hpointL, hQzero, hQframe⟩ :=
    compatible_original_graph_boundary_lift_constructs_algebraic_coordinates
      H hrank p hY I (Nat.lt_trans Nat.zero_lt_one hd) hH hN hind hGauss h c qinv hh hc hqinv
        (C := Cᵣ) (A := Jᵣ) (G := Gᵣ) (vᵣ) (Φ₀ hT).toRingHom g hg hcoords hJalg p₀ hpoint hp0 b hpb
  let F : Type u := projectivePrimeRatioField Q (some b)
  let hF : Field F := projectivePrimeRatioFieldField Q (some b)
  letI : Field F := hF
  let aJF : Algebra Jᵣ F := projectivePrimeRatioFieldCoefficientAlgebra Q (some b)
  let ξ : Option (Fin 4) → F := projectivePrimeRatioCoordinate Q (some b)
  have hξF := projectivePrimeRatioCoordinate_ne_zero Q (some b) hQb
  exact ⟨hT, α, hα, γ, hγ, η, hηX, hηlevel, hηE, g, hg, hgK, hgC, hJalg,
    F, hF, aJF, ξ, hξF, hQideal, hRalg, hpointL, hQzero, hQframe⟩

end DimensionFourDependence
