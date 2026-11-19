import DimensionFourDependence.TensorPencilHyperplaneMultiplicity
import DimensionFourDependence.ExtendedGaussNormalizationStalkMaps
import DimensionFourDependence.LocalEquivOrderTransport

/-! # Hyperplane multiplicity in the actual global normalized pencil stalks

The section is pulled back by the actual global normalization morphism.
The existing original tensor-chart stalk identification retains its
entire original affine linear value. Intrinsic codimension one then gives
the pencil-degree bound on its order in the actual global stalk.
-/

namespace DimensionFourDependence

universe u

open AlgebraicGeometry MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "N₀" => normalizationRing T₀
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "zₑ" q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q

/-- The exact affine linear value of the extended hyperplane in the
original tensor chart, with its extended-field coefficients. -/
noncomputable def originalTensorPencilHyperplaneValue (b : E) (c : Fin 3 → E) : T₀ :=
  algebraMap E T₀ b + ∑ i, algebraMap E T₀ (c i) * originalTensorPencilCoordinate H I E s i

/-- The actual global normalization pullback of the hyperplane's
regular coefficient in its chosen original coordinate frame. -/
noncomputable def extendedClosedGaussNormalizationHyperplaneGerm
    (q : PrimeSpectrum N₀) (b : E) (c : Fin 3 → E) : (Nₑ).presheaf.stalk (zₑ q) :=
  extendedClosedGaussNormalizationPencilGerm H I E hH e s q
    ((extendedClosedGaussPencilTensorChartSectionEquiv H I E hH e s).symm
      (originalTensorPencilHyperplaneValue H I E s b c))

/-- The actual global hyperplane coefficient has exactly its original
affine linear value in the original normalization prime localization. -/
theorem extendedClosedGaussNormalizationHyperplaneGerm_local_value
    (q : PrimeSpectrum N₀) (b : E) (c : Fin 3 → E) :
    extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q
      (extendedClosedGaussNormalizationHyperplaneGerm H I E hH e s q b c) =
      algebraMap T₀ (Localization.AtPrime q.asIdeal)
        (originalTensorPencilHyperplaneValue H I E s b c) := by
  let z := originalTensorPencilHyperplaneValue H I E s b c
  let φ := extendedClosedGaussPencilTensorChartSectionEquiv H I E hH e s
  have h := extendedClosedGaussNormalizationTensorChartStalkIso_pencil_germ
    H I E hH e s q (φ.symm z)
  exact h.trans ((congrArg
    (fun r : T₀ => algebraMap N₀ (Localization.AtPrime q.asIdeal) (algebraMap T₀ N₀ r))
    (φ.apply_symm_apply z)).trans
      (IsScalarTower.algebraMap_apply T₀ N₀ (Localization.AtPrime q.asIdeal) z).symm)

/-- Intrinsic codimension one of the actual global normalization point
is height one of its original normalization prime. -/
theorem extendedClosedGaussNormalizationTensorChartPoint_height_one
    (q : PrimeSpectrum N₀) (hq : Order.coheight (zₑ q) = 1) : q.asIdeal.height = 1 := by
  have hdim : ringKrullDim ((Nₑ).presheaf.stalk (zₑ q)) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hq]
    rfl
  have h := ringKrullDim_eq_of_ringEquiv
    (extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (Localization.AtPrime q.asIdeal)] at h
  have hh : (q.asIdeal.height : WithBot ℕ∞) = 1 := h.symm.trans hdim
  exact_mod_cast hh

/-- At an actual codimension-one point of the normalized extended
pencil, every nonzero hyperplane coefficient has order at most the
original pencil degree in the actual global stalk. Its vanishing at the
prime is derived from any positive order bound. -/
theorem actual_global_normalized_pencil_hyperplane_order_le_degree
    (hGauss : gaussImageDimension H I = 1)
    (p q : MvPolynomial (Fin 4) K) {D : ℕ}
    (hq0 : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)
    (Q : PrimeSpectrum N₀) (hcodim : Order.coheight (zₑ Q) = 1)
    (b : E) (c : Fin 3 → E)
    (hz0 : originalTensorPencilHyperplaneValue H I E s b c ≠ 0)
    (a : ℕ) (horder : extendedClosedGaussNormalizationHyperplaneGerm H I E hH e s Q b c ∈
      (IsLocalRing.maximalIdeal ((Nₑ).presheaf.stalk (zₑ Q))) ^ a) : a ≤ D := by
  by_cases ha : a = 0
  · subst a
    exact Nat.zero_le _
  let B := Localization.AtPrime Q.asIdeal
  let β := extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s Q
  have hlocal : algebraMap T₀ B (originalTensorPencilHyperplaneValue H I E s b c) ∈
      (IsLocalRing.maximalIdeal B) ^ a := by
    have h := (local_equiv_maximalIdeal_pow_mem_iff
      (A := (Nₑ).presheaf.stalk (zₑ Q)) (B := Localization.AtPrime Q.asIdeal) β
      (extendedClosedGaussNormalizationHyperplaneGerm H I E hH e s Q b c) a).mpr horder
    have hv : β (extendedClosedGaussNormalizationHyperplaneGerm H I E hH e s Q b c) =
        algebraMap T₀ B (originalTensorPencilHyperplaneValue H I E s b c) :=
      extendedClosedGaussNormalizationHyperplaneGerm_local_value H I E hH e s Q b c
    exact Eq.mp (congrArg (fun t : B => t ∈ (IsLocalRing.maximalIdeal B) ^ a) hv) h
  have hz : algebraMap T₀ N₀ (originalTensorPencilHyperplaneValue H I E s b c) ∈ Q.asIdeal := by
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff B Q.asIdeal _).mp
    exact Eq.mp (congrArg (fun t : B => t ∈ IsLocalRing.maximalIdeal B)
      (IsScalarTower.algebraMap_apply T₀ N₀ B
        (originalTensorPencilHyperplaneValue H I E s b c)))
      ((IsLocalRing.maximalIdeal B).pow_le_self ha hlocal)
  have hQ := extendedClosedGaussNormalizationTensorChartPoint_height_one H I E hH e s Q hcodim
  exact actual_original_tensor_pencil_hyperplane_order_le_degree H I E hH e hGauss
    p q hq0 hrel hpH hqH ht s b c Q.asIdeal hQ hz0 hz a hlocal

end DimensionFourDependence
