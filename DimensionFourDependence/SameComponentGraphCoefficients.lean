import DimensionFourDependence.ComponentSourceRealizationTransport
import DimensionFourDependence.AlgebraicCoefficientEmbedding
import DimensionFourDependence.CompatibleGeometricSource
import DimensionFourDependence.ClosedGaussCoefficientTensor
import DimensionFourDependence.AlgebraicSourceConstantLift

/-! # The same geometric component retains the entire original graph coefficient field -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] coefficientFieldScalarTower

universe u

set_option maxHeartbeats 400000
set_option quotPrecheck false
set_option synthInstance.maxHeartbeats 10000
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
    {B Z : Type u} [Field B] [Field Z] [IsAlgClosed B] [Algebra B Z]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "D₀" => polynomialOutputField H
local notation "C₀" => closedGaussParameterField H I
local notation "Y" => (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc)))
local notation "L" => coefficientField (K := K) (Y)
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh

include hrank hY

omit hrank in
/-- The original closed Gauss inclusion in the graph coefficient
field has exactly its original source value. -/
theorem original_closed_gauss_graph_inclusion_source_value (c : C₀) :
    algebraMap (L) S₀ ((a) c) = (c : S₀) := by
  rw [IntermediateField.algebraMap_apply]
  exact IntermediateField.coe_inclusion
    (actual_closed_gauss_field_le_graph_coefficient_field H I p hY h hh) c

/-- The actual full component and its original source map recover
all original graph coefficients as constants and retain the full output
field action on every original output-field element. -/
theorem full_generic_component_original_source_constructs_graph_coefficient_embedding
    (δ : D₀ →+* B) (f : S₀ →+* Z) (x : Fin 4 → Z)
    (hfK : ∀ c : K, f (algebraMap K S₀ c) = algebraMap B Z (δ (algebraMap K D₀ c)))
    (hfx : ∀ i, f (rationalCoordinate (K := K) i) = x i) :
    letI : Algebra D₀ B := δ.toAlgebra
    fiberVanishingIdeal («L» := B) x ∈
      (extendCoefficientIdeal B (fiberVanishingIdeal («L» := D₀)
        (rationalCoordinate (K := K) (n := 4)))).minimalPrimes →
    ∃ g : (L) →+* B, (∀ l : L, algebraMap B Z (g l) = f (l : S₀)) ∧
      ∀ d : D₀, f (d : S₀) = algebraMap B Z (δ d) := by
  classical
  letI : Algebra D₀ B := δ.toAlgebra
  intro hcomponent
  letI : Algebra D₀ Z := ((algebraMap B Z).comp δ).toAlgebra
  letI : IsScalarTower D₀ B Z := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨fD, hfD⟩ := full_generic_component_coordinates_construct_source_realization H x hcomponent
  have hground (c : K) : fD (algebraMap K S₀ c) = f (algebraMap K S₀ c) := by
    change fD (algebraMap D₀ S₀ (algebraMap K D₀ c)) = _
    rw [fD.commutes]
    exact (hfK c).symm
  have hsame : fD.toRingHom = f :=
    rational_source_ringHom_ext_original_coefficients_and_coordinates _ _ hground
      (fun i => (hfD i).trans (hfx i).symm)
  let H₀ : Fin 4 → S₀ := fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)
  have hr : (rationalJacobian H₀).rank = 3 := by
    rw [rationalJacobian_polynomial H]
    exact hrank
  have hAlg (l : L) : IsAlgebraic B (f (l : S₀)) := by
    have hl : IsAlgebraic D₀ (l : S₀) :=
      (fullOutput_algebraic_iff_coefficientField H₀ hr p hY (l : S₀)).mpr l.property
    have hz : IsAlgebraic B (fD (l : S₀)) := (IsAlgebraic.algHom fD hl).tower_top B
    have he : fD (l : S₀) = f (l : S₀) := DFunLike.congr_fun hsame (l : S₀)
    rwa [he] at hz
  obtain ⟨g, hg⟩ := algebraic_source_coefficient_values_construct_constant_embedding («L» := L) f hAlg
  refine ⟨g, hg, ?_⟩
  intro d
  have he : fD (d : S₀) = f (d : S₀) := DFunLike.congr_fun hsame (d : S₀)
  exact he.symm.trans (fD.commutes d)

/-- The same actual source embedding and full component construct
the original graph coefficient embedding into the geometric constants.
It agrees with the specified finite coefficient realization on the
entire closed Gauss field. Neither a new source realization nor an
unrelated closed-field conjugate is chosen. -/
theorem same_full_generic_component_constructs_compatible_graph_coefficient_embedding
    (δ : D₀ →+* B) (σ : E →+* B) (f : S₀ →+* Z) (x : Fin 4 → Z)
    (hfK : ∀ c : K, f (algebraMap K S₀ c) = algebraMap B Z (δ (algebraMap K D₀ c)))
    (hfx : ∀ i, f (rationalCoordinate (K := K) i) = x i)
    (hfC : ∀ c : C₀, f (c : S₀) = algebraMap B Z (σ (algebraMap C₀ E c))) :
    letI : Algebra D₀ B := δ.toAlgebra
    fiberVanishingIdeal («L» := B) x ∈
      (extendCoefficientIdeal B (fiberVanishingIdeal («L» := D₀)
        (rationalCoordinate (K := K) (n := 4)))).minimalPrimes →
    ∃ g : (L) →+* B,
      (∀ l : L, algebraMap B Z (g l) = f (l : S₀)) ∧
      (∀ c : K, g (algebraMap K (L) c) = δ (algebraMap K D₀ c)) ∧
      (∀ c : C₀, g ((a) c) = σ (algebraMap C₀ E c)) ∧
      ∀ (d : D₀) (l : L), (l : S₀) = (d : S₀) → g l = δ d := by
  letI : Algebra D₀ B := δ.toAlgebra
  intro hcomponent
  obtain ⟨g, hg, hfD⟩ := full_generic_component_original_source_constructs_graph_coefficient_embedding
    H hrank p hY δ f x hfK hfx hcomponent
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · intro c
    apply constant_embedding_value_eq_of_source_value f g hg
    exact (congrArg f (IsScalarTower.algebraMap_apply K (L) S₀ c).symm).trans (hfK c)
  · intro c
    apply constant_embedding_value_eq_of_source_value f g hg
    exact (congrArg f (original_closed_gauss_graph_inclusion_source_value H I p hY h hh c)).trans (hfC c)
  · intro d l hl
    apply constant_embedding_value_eq_of_source_value f g hg
    exact (congrArg f hl).trans (hfD d)

end DimensionFourDependence
