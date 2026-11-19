import DimensionFourDependence.AffineCoordinateStalk
import DimensionFourDependence.OriginalSourcePrimeRegularOrders
import DimensionFourDependence.ExtendedGaussProjectiveStalkMaps
import DimensionFourDependence.ExtendedGaussSourcePoint

/-! # The actual original projective source stalk and its complete pullback

The source-image stalk is the localization of its original ratio ring.
The actual geometric stalk map agrees there with the canonical local
map induced by the specified original tensor source homomorphism.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "x₀" => rationalCoordinate (K := K) (n := 4)
local notation "R₀" => projectiveCoordinateChartAlgebra (C := K) x₀ (s.symm none)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀) x₀ (s.symm none)
local notation "N₀" => normalizationRing (S₀ ⊗[C₀] E)
local notation "Pₖ" => AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "mₑ" => extendedClosedGaussNormalizationSourceMorphism H I E hH e
local notation "zₑ" q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q
local notation "Q₀" q:max => extendedClosedGaussTensorNormalizationSourcePrime H I E s q
local notation "Uₖ" => Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X (s.symm none))
local notation "hUₖ" => Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) K)
  (X (s.symm none)) (isHomogeneous_X (R := K) _) (by omega)

/-- The actual source-image prime, expressed using the specified
original source point with its primality already retained. -/
theorem extendedClosedGaussNormalization_source_prime_named
    (q : PrimeSpectrum N₀) :
    ((hUₖ).primeIdealOf ⟨(mₑ) (zₑ q),
      extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q⟩).asIdeal =
      (Q₀ q).asIdeal.comap
        (originalProjectiveAffineSectionEquiv (K := K) (s.symm none)).toRingHom := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact by
    rw [extendedClosedGaussTensorNormalizationSourcePrime_asIdeal]
    exact extendedClosedGaussNormalizationTensorChartPoint_source_prime H I E hH e s q

/-- The actual original projective source stalk is its original
ratio-ring prime localization, at the actual source-image point. -/
@[irreducible] noncomputable def extendedClosedGaussNormalizationSourceStalkEquiv
    (q : PrimeSpectrum N₀) :
    (Pₖ).presheaf.stalk ((mₑ) (zₑ q)) ≃+* Localization.AtPrime (Q₀ q).asIdeal := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact affineOpenCoordinateStalkEquiv ⟨Uₖ, hUₖ⟩ (CommRingCat.of R₀)
    (originalProjectiveAffineSectionEquiv (K := K) (s.symm none))
    ⟨(mₑ) (zₑ q), extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q⟩
    (Q₀ q) (extendedClosedGaussNormalization_source_prime_named H I E hH e s q)

/-- The original source-stalk coordinates preserve every actual
projective section germ and its original ratio-ring value. -/
theorem extendedClosedGaussNormalizationSourceStalkEquiv_germ
    (q : PrimeSpectrum N₀) (r : Γ(Pₖ, Uₖ)) :
    extendedClosedGaussNormalizationSourceStalkEquiv H I E hH e s q
      ((Pₖ).presheaf.germ Uₖ ((mₑ) (zₑ q))
        (extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q) r) =
      algebraMap R₀ (Localization.AtPrime (Q₀ q).asIdeal)
        (originalProjectiveAffineSectionEquiv (K := K) (s.symm none) r) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact by
    have h := affineOpenCoordinateStalkEquiv_germ ⟨Uₖ, hUₖ⟩ (CommRingCat.of R₀)
      (originalProjectiveAffineSectionEquiv (K := K) (s.symm none))
      ⟨(mₑ) (zₑ q), extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q⟩
      (Q₀ q) (extendedClosedGaussNormalization_source_prime_named H I E hH e s q) r
    unfold extendedClosedGaussNormalizationSourceStalkEquiv
    convert! h using 1

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Every actual source section germ has its specified original
source value under the actual geometric stalk pullback. -/
theorem extendedClosedGaussNormalizationSourceStalkMap_germ
    (q : PrimeSpectrum N₀) (r : Γ(Pₖ, Uₖ)) :
    extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q
      ((mₑ).stalkMap (zₑ q)
        ((Pₖ).presheaf.germ Uₖ ((mₑ) (zₑ q))
          (extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q) r)) =
      algebraMap N₀ (Localization.AtPrime q.asIdeal)
        (extendedClosedGaussTensorNormalizationSourceHom H I E s
          (originalProjectiveAffineSectionEquiv (K := K) (s.symm none) r)) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact by
    let b : (Nₑ).presheaf.stalk (zₑ q) → Localization.AtPrime q.asIdeal :=
      fun a => extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q a
    have h0 := congrArg b
      (extendedClosedGaussNormalizationProjectiveSourceGerm_stalkMap H I E hH e s q r)
    have h1 := congrArg b
      (extendedClosedGaussNormalizationProjectiveSourceGerm_eq_source_germ H I E hH e s q r)
    have h2 := extendedClosedGaussNormalizationTensorChartStalkIso_source_germ H I E hH e s q
      (projectiveAmbientSectionToSource (C := K) x₀ (s.symm none)
        (source_rationalCoordinate_ne_zero _) r)
    simpa only [originalProjectiveAffineSectionEquiv_apply] using h0.trans (h1.trans h2)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- On the whole actual source stalk, the geometric source pullback
is precisely the canonical map of the original prime localizations. -/
theorem extendedClosedGaussNormalizationSourceStalkEquiv_stalkMap
    (q : PrimeSpectrum N₀) (z : (Pₖ).presheaf.stalk ((mₑ) (zₑ q))) :
    extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q
        ((mₑ).stalkMap (zₑ q) z) =
      Localization.localRingHom (Q₀ q).asIdeal q.asIdeal
        (extendedClosedGaussTensorNormalizationSourceHom H I E s)
        (extendedClosedGaussTensorNormalizationSourcePrime_asIdeal H I E s q)
        (extendedClosedGaussNormalizationSourceStalkEquiv H I E hH e s q z) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact by
    have hgen := extendedClosedGaussNormalizationSourceStalkMap_germ H I E hH e s q
    have h := affineOpenCoordinateStalkEquiv_stalkMap
      (U := ⟨Uₖ, hUₖ⟩) (R := CommRingCat.of R₀) (B := CommRingCat.of N₀)
      (originalProjectiveAffineSectionEquiv (K := K) (s.symm none)) mₑ (zₑ q)
      (extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q)
      (Q₀ q) q (extendedClosedGaussNormalization_source_prime_named H I E hH e s q)
      (extendedClosedGaussTensorNormalizationSourceHom H I E s)
      (extendedClosedGaussTensorNormalizationSourcePrime_asIdeal H I E s q)
      (extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q) hgen z
    unfold extendedClosedGaussNormalizationSourceStalkEquiv
    convert! h using 1

end DimensionFourDependence
