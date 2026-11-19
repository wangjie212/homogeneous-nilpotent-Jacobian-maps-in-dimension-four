import DimensionFourDependence.CharacteristicAlgebraicGraphBoundary
import DimensionFourDependence.CharacteristicBoundaryDirection
import DimensionFourDependence.ProjectiveDirectionIdealContraction

/-! # The actual root-divisor intersection has the complete characteristic point ideal -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 5000
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

local instance nativeCharacteristicIntersectionIdealDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
local instance nativeCharacteristicIntersectionIdealIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeCharacteristicIntersectionIdealExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

noncomputable local instance nativeCharacteristicIntersectionIdealOriginalAlgebra : Algebra K (N).functionField :=
  extendedClosedGaussOriginalSourceAlgebra H I E hH e

noncomputable local instance nativeCharacteristicIntersectionIdealExtendedSMul : SMul E (N).functionField :=
  (extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e).toSMul
noncomputable local instance nativeCharacteristicIntersectionIdealOriginalSMul : SMul K (N).functionField :=
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

local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH
  (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss
local notation "cN" => closedGaussCanonicalRootNumerator H I p hY h hh e E
local notation "x₀" z:max b:max hb:max => fun i => IsLocalRing.residue ((N).presheaf.stalk z)
  (nativeProjectiveCoordinateGerm H I E hH e z b hb i)

include hrank

/-- Apply the original proportional-power comparison to the algebraic
lift of this very native intersection. Exact coefficient contraction
identifies its whole original-coordinate point ideal with that of the
same characteristic vector over the given Gauss coefficient field. -/
theorem actual_characteristic_root_intersection_has_same_characteristic_point_ideal
    (hN : IsNilpotent (jac H))
    (c q k : L)
    (hc : (c : S₀) = firstFiberInvariantInChart p
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))) hY h) (hc0 : c ≠ 0)
    (hq : (q : S₀) = secondFiberInvariant p
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))) hY h c q)
    (S M : Fin 4 → E) (r : (N).functionField)
    (hpower : r ^ d = aeval (w) ((O) S))
    (hmNative : aeval (w) ((O) M) ≠ 0)
    (hformula : r = aeval (w) ((O) (cN)) * aeval (w) (L₀) / aeval (w) ((O) M))
    (hMN : LinearIndependent E ![rulingFormRestriction (LinearMap.ker (A₀).toLin') M,
      rulingFormRestriction (LinearMap.ker (A₀).toLin') (cN)])
    (β : E) (hβ : β ≠ 0)
    (hSN : rulingFormRestriction (LinearMap.ker (A₀).toLin') S =
      β • rulingFormRestriction (LinearMap.ker (A₀).toLin') (cN))
    (z : N) (b : Fin 4) (hb : z ∈ U b)
    (hboundary : NativeCharacteristicOriginalFiberBoundaryAtPoint H I E hH e hd hind hGauss r z b hb)
    (W : Fin 4 → E) (hW0 : W ≠ 0)
    (hW : W ∈ extendedClosedGaussChosenCharacteristicSubspace H I E hH
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss) :
    letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
    (projectiveFieldPointIdeal (E := E) (x₀ z b hb)).toIdeal =
      (projectiveFieldPointIdeal (E := E) W).toIdeal := by
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
  obtain ⟨hT, α, hα, γ, hγ, η, hηX, hηlevel, hηE,
    g, hg, hgK, hgC, hJalg, F, hF, aJF, ξ, hξ, hWhole, hFalg, hpointF, hzero, hframe⟩ :=
      actual_characteristic_original_boundary_constructs_algebraic_graph_boundary
        H hrank I p hY h hh E hH e hd hind hGauss hN c q hc hq r z b hb hboundary
  letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
  letI : Algebra Cᵣ Gᵣ := γ.toRingHom.toAlgebra
  letI : SMul Cᵣ Gᵣ := γ.toRingHom.toAlgebra.toSMul
  letI : Field F := hF
  letI : Algebra Jᵣ F := aJF
  letI : SMul Jᵣ F := aJF.toSMul
  letI : Algebra (L) F := ((algebraMap Jᵣ F).comp g).toAlgebra
  letI : SMul (L) F := (((algebraMap Jᵣ F).comp g).toAlgebra).toSMul
  letI : Algebra.IsAlgebraic (L) F := hFalg
  let σ : E →+* F := (algebraMap Jᵣ F).comp
    ((algebraMap Cᵣ Jᵣ).comp (RatFunc.C.comp RatFunc.C))
  letI : Algebra E F := σ.toAlgebra
  letI : SMul E F := σ.toAlgebra.toSMul
  letI : Algebra K F := ((algebraMap (L) F).comp (algebraMap K (L))).toAlgebra
  letI : SMul K F := (((algebraMap (L) F).comp (algebraMap K (L))).toAlgebra).toSMul
  letI : IsScalarTower K (L) F := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra C₀ F := ((algebraMap (L) F).comp (a).toRingHom).toAlgebra
  letI : SMul C₀ F := (((algebraMap (L) F).comp (a).toRingHom).toAlgebra).toSMul
  have hcompat : IsScalarTower C₀ E F := by
    apply IsScalarTower.of_algebraMap_eq
    intro t
    change algebraMap Jᵣ F (g ((a) t)) =
      algebraMap Jᵣ F (algebraMap Cᵣ Jᵣ (RatFunc.C (RatFunc.C (algebraMap C₀ E t))))
    exact congrArg (algebraMap Jᵣ F) (hgC t)
  have hchar := actual_proportional_power_boundary_has_same_original_characteristic_ideal
    H hrank I p hY h hh E hd hH hind hGauss e F hN hcompat c q k hc hc0 hq hk
      S M r hpower hmNative hformula hMN β hβ hSN ξ hξ hpointF hzero b hframe W hW0 hW
  let κ := IsLocalRing.ResidueField ((N).presheaf.stalk z)
  let T := RatFunc (RatFunc κ)
  letI : Algebra E Cᵣ := (RatFunc.C.comp RatFunc.C).toAlgebra
  letI : SMul E Cᵣ := ((RatFunc.C.comp RatFunc.C).toAlgebra).toSMul
  letI : Algebra Cᵣ F := ((algebraMap Jᵣ F).comp (algebraMap Cᵣ Jᵣ)).toAlgebra
  letI : SMul Cᵣ F := (((algebraMap Jᵣ F).comp (algebraMap Cᵣ Jᵣ)).toAlgebra).toSMul
  letI : IsScalarTower E Cᵣ F := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra Cᵣ T := η.toAlgebra
  letI : SMul Cᵣ T := η.toAlgebra.toSMul
  letI : Algebra E T := ((RatFunc.C.comp RatFunc.C).comp (algebraMap E κ)).toAlgebra
  letI : SMul E T := (((RatFunc.C.comp RatFunc.C).comp (algebraMap E κ)).toAlgebra).toSMul
  letI : IsScalarTower E Cᵣ T := IsScalarTower.of_algebraMap_eq (fun t => (hηE t).symm)
  have hDirs := original_direction_ideal_eq_of_extended_whole_coordinate_ideal
    (E := E) (C := Cᵣ) ξ (ξ₀ z b hb) hWhole
  let f : κ →ₐ[E] T := { RatFunc.C.comp RatFunc.C with commutes' := fun _ => rfl }
  have htransport := projectiveFieldPointIdeal_algHom (x₀ z b hb) f
  have hNative : (projectiveFieldPointIdeal (E := E)
      (fun i => (ξ₀ z b hb) (some i))).toIdeal =
        (projectiveFieldPointIdeal (E := E) (x₀ z b hb)).toIdeal := htransport
  exact hNative.symm.trans (hDirs.symm.trans hchar)

end DimensionFourDependence
