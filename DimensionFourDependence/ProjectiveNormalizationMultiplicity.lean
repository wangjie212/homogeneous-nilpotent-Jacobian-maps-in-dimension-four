import DimensionFourDependence.ProjectiveChartCommonFactor
import DimensionFourDependence.NormalizationLocalSourceOrders

/-! # Normalization orders force the original homogeneous factor degree

The original homogeneous sections are represented in the actual source
chart. Exact source-local order transport at a given normalization prime
then yields an actual homogeneous prime-power divisor of g and the bound
a <= degree(g). The polynomial g remains the original common factor.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

open MvPolynomial

section Transport

variable {K : Type*} [Field K]

/-- Any checked original-source local order map carries the actual
projective section order bounds back to the original homogeneous factor. -/
theorem projective_transported_orders_common_factor_degree
    (s : Fin 4 ≃ Option (Fin 3))
    (H P : Fin 4 → MvPolynomial (Fin 4) K) (g : MvPolynomial (Fin 4) K) {c d : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P d)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (δ : MvPolynomial (Fin 3) K) (hδ : Irreducible δ)
    (Q : Ideal (projectiveCoordinateChartAlgebra (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none))) [Q.IsPrime]
    (hQ : Q = Ideal.span {projectiveSourceFullChartCoordinateEquiv s δ})
    (T : Type*) [CommRing T] [IsLocalRing T]
    [Algebra (projectiveCoordinateChartAlgebra (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none)) T]
    (ι : Localization.AtPrime Q →ₐ[projectiveCoordinateChartAlgebra (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none)] T)
    (hpower : ∀ (x : Localization.AtPrime Q) (b : ℕ),
      ι x ∈ (IsLocalRing.maximalIdeal T) ^ b ↔
        x ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ b)
    (a : ℕ) (horder : ∀ i, algebraMap _ T (projectiveSourceSectionHom s (H i)) ∈
      (IsLocalRing.maximalIdeal T) ^ a) :
    projectiveSourceHomogeneousDivisor s δ ^ a ∣ g ∧
      a * δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  apply projective_source_divisor_orders_common_factor_degree s H P g hg hgh hP hprim hHP δ hδ Q hQ a
  intro i
  apply (hpower (algebraMap _ (Localization.AtPrime Q) (projectiveSourceSectionHom s (H i))) a).mp
  rw [ι.commutes]
  exact horder i

end Transport

section Normalization

variable {K : Type*} [Field K] (s : Fin 4 ≃ Option (Fin 3))

local notation "R₀" => projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)

variable (Q : Ideal (projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none))) [Q.IsPrime]

local notation "O₀" => Localization.AtPrime Q

/-- The given normalization prime's proved source-order comparison
implies original homogeneous prime-power common-factor divisibility and
the original degree bound from its actual projective section orders. -/
theorem normalization_projective_section_orders_common_factor_degree
    {S B F L : Type*} [CommRing S] [IsDiscreteValuationRing O₀]
    [CommRing B] [IsDedekindDomain B] [Field F] [Field L]
    [Algebra R₀ S] [Algebra R₀ B] [Algebra S B] [Algebra O₀ B]
    [IsScalarTower R₀ S B] [IsScalarTower R₀ O₀ B]
    [Algebra S F] [Algebra B F] [IsScalarTower S B F] [IsFractionRing B F]
    [Algebra.Etale O₀ B] [Algebra O₀ L] [IsFractionRing O₀ L]
    (H P : Fin 4 → MvPolynomial (Fin 4) K) (g : MvPolynomial (Fin 4) K) {c d : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P d)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (δ : MvPolynomial (Fin 3) K) (hδ : Irreducible δ)
    (hQ : Q = Ideal.span {projectiveSourceFullChartCoordinateEquiv s δ}) (a : ℕ)
    (hmodel : NormalizationLocalSourceOrders (R := R₀) (S := S) (O := O₀)
      (B := B) (F := F) (L := L) Q) :
    letI : Algebra R₀ (integralClosure S F) :=
      ((algebraMap S (integralClosure S F)).comp (algebraMap R₀ S)).toAlgebra
    ∀ (q : Ideal (integralClosure S F)) [q.IsPrime] [q.LiesOver Q],
      (∀ i, algebraMap R₀ (Localization.AtPrime q) (projectiveSourceSectionHom s (H i)) ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ a) →
      projectiveSourceHomogeneousDivisor s δ ^ a ∣ g ∧
        a * δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  let : Algebra R₀ (integralClosure S F) :=
    ((algebraMap S (integralClosure S F)).comp (algebraMap R₀ S)).toAlgebra
  intro q hq hlie horder
  let : Algebra (integralClosure S F) B :=
    (integralClosureToNormalLocalHom (S := S) (A := B) (F := F)).toRingHom.toAlgebra
  obtain ⟨hprime, hPlie, e, _, _, hpower, _⟩ := @hmodel q hq hlie
  let w := q.map (algebraMap (integralClosure S F) B)
  let : w.IsPrime := hprime
  let : w.LiesOver (IsLocalRing.maximalIdeal O₀) := hPlie
  let : IsScalarTower R₀ O₀ (Localization.AtPrime w) :=
    IsScalarTower.to₁₂₄ R₀ O₀ B (Localization.AtPrime w)
  exact projective_transported_orders_common_factor_degree s H P g hg hgh hP hprim hHP δ hδ Q hQ
    (Localization.AtPrime q) (localEquivSourceAlgHom (O := O₀) e) hpower a horder

end Normalization

end DimensionFourDependence
