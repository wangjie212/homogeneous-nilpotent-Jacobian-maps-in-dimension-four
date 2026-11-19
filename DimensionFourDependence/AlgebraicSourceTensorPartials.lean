import DimensionFourDependence.AffineSourceConeForm
import DimensionFourDependence.AlgebraicPartial

/-! # The actual algebraic source tensor constructs original coordinate partials

Algebraic coefficient base change is algebraic over the original source;
passing to its fraction field preserves algebraicity. Thus the actual
source field carrying the constructed cone formula has uniquely extended
original coordinate partials, with their coordinate values and commutation.
-/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

section Algebraic

variable {C S L : Type*} [Field C] [Field S] [Field L]
    [Algebra C S] [Algebra C L] [Algebra.IsAlgebraic C L] [IsDomain (S ⊗[C] L)]

/-- The fraction field of the actual algebraic coefficient base
change is algebraic over the original source field. -/
theorem algebraic_source_tensor_fraction_isAlgebraic :
    Algebra.IsAlgebraic S (FractionRing (S ⊗[C] L)) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨a, b, _hb, rfl⟩ := IsFractionRing.div_surjective (A := S ⊗[C] L) x
  have ha : IsAlgebraic S (algebraMap (S ⊗[C] L) (FractionRing (S ⊗[C] L)) a) :=
    (Algebra.IsAlgebraic.isAlgebraic (R := S) a).algebraMap
  have hb : IsAlgebraic S (algebraMap (S ⊗[C] L) (FractionRing (S ⊗[C] L)) b) :=
    (Algebra.IsAlgebraic.isAlgebraic (R := S) b).algebraMap
  exact mem_algebraicClosure_iff.mp ((algebraicClosure S (FractionRing (S ⊗[C] L))).div_mem
    (mem_algebraicClosure_iff.mpr ha) (mem_algebraicClosure_iff.mpr hb))

end Algebraic

universe u

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (L : Type u) [Field L] [Algebra (closedGaussParameterField H I) L]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) L]

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] L
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I L

local instance algebraicSourceTensorPartialsDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I L).isDomain

/-- The actual source field carrying the complete cone formula is
an algebraic extension of the original rational source field. -/
theorem closed_gauss_affine_source_fraction_isAlgebraic : Algebra.IsAlgebraic S₀ F₀ :=
  algebraic_source_tensor_fraction_isAlgebraic

/-- The actual algebraic Gauss source field constructs the original
four coordinate partials, preserving every original rational derivative
and all mixed-partial commutation identities. -/
theorem closed_gauss_affine_source_fraction_constructs_original_coordinate_partials :
    letI : Algebra K F₀ := ((algebraMap S₀ F₀).comp (algebraMap K S₀)).toAlgebra
    letI : SMul K S₀ := (inferInstance : Algebra K S₀).toSMul
    letI : SMul S₀ F₀ := (inferInstance : Algebra S₀ F₀).toSMul
    letI : SMul K F₀ := (inferInstance : Algebra K F₀).toSMul
    letI : Module K F₀ := (inferInstance : Algebra K F₀).toModule
    letI : IsScalarTower K S₀ F₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI : Algebra.IsAlgebraic S₀ F₀ := closed_gauss_affine_source_fraction_isAlgebraic H I L
    ∃ D : Fin 4 → Derivation K F₀ F₀,
      (∀ i j, D i ((xₐ) j) = if j = i then 1 else 0) ∧
      (∀ i (s : S₀), D i (algebraMap S₀ F₀ s) = algebraMap S₀ F₀ (rationalPartial (K := K) i s)) ∧
      ∀ i j (s : F₀), D i (D j s) = D j (D i s) := by
  let : Algebra K F₀ := ((algebraMap S₀ F₀).comp (algebraMap K S₀)).toAlgebra
  let : SMul K S₀ := (inferInstance : Algebra K S₀).toSMul
  let : SMul S₀ F₀ := (inferInstance : Algebra S₀ F₀).toSMul
  let : SMul K F₀ := (inferInstance : Algebra K F₀).toSMul
  let : Module K F₀ := (inferInstance : Algebra K F₀).toModule
  let : IsScalarTower K S₀ F₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra.IsAlgebraic S₀ F₀ := closed_gauss_affine_source_fraction_isAlgebraic H I L
  refine ⟨fun i : Fin 4 => algebraicPartial (K := K) (n := 4) F₀ i, ?_, ?_, ?_⟩
  · intro i j
    change algebraicPartial (K := K) F₀ i (algebraMap S₀ F₀ (rationalCoordinate (K := K) j)) = _
    exact algebraicPartial_coordinate F₀ i j
  · intro i s
    exact algebraicPartial_extends (K := K) (n := 4) F₀ i s
  · intro i j s
    exact algebraicPartials_commute (K := K) (n := 4) F₀ i j s

end DimensionFourDependence
