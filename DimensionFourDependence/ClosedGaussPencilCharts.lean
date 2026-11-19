import DimensionFourDependence.ClosedGaussPencilIntegrality
import DimensionFourDependence.ProjectivePrincipalChart

/-! # Exact projective pencil charts and their finite normalizations

The index equivalence chooses any one of the four source coordinates as
the nonzero homogenizing coordinate. All three chart ratios remain the
actual original-source rational functions. Their entire relation ideal is
the dehomogenized actual pencil equation, and their normalization is finite,
normal, Noetherian, and has the same fraction field.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

local notation "R" => MvPolynomial (Fin 4) K
local notation "F" => FractionRing (MvPolynomial (Fin 4) K)

/-- The three actual source ratios on a chosen projective source chart. -/
noncomputable def closedGaussPencilChartPoint (s : Fin 4 ≃ Option (Fin 3)) : Fin 3 → F :=
  fun i => rationalCoordinate (K := K) (s.symm (some i)) /
    rationalCoordinate (K := K) (s.symm none)

/-- The actual pencil equation on the chosen standard affine chart. -/
noncomputable def closedGaussPencilChartEquation
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (p q : R)
    (s : Fin 4 ≃ Option (Fin 3)) : MvPolynomial (Fin 3) (closedGaussParameterField H I) :=
  projectiveDehomogenize (rename s (closedGaussPencilEquation H I e p q))

/-- Reindexing the original source preserves its exact principal pencil
relation ideal. -/
theorem actual_closed_gauss_pencil_reindexed_relation_ideal
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (p q : R)
    (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X = algebraMap R F p / algebraMap R F q)
    (s : Fin 4 ≃ Option (Fin 3)) :
    RingHom.ker (aeval (fun j => rationalCoordinate (K := K) (s.symm j)) :
      MvPolynomial (Option (Fin 3)) (closedGaussParameterField H I) →ₐ[closedGaussParameterField H I] F) =
        Ideal.span {rename s (closedGaussPencilEquation H I e p q)} := by
  let C := closedGaussParameterField H I
  let E := renameEquiv C s
  let G := closedGaussPencilEquation H I e p q
  ext P
  have heval : aeval (fun j => rationalCoordinate (K := K) (s.symm j)) P =
      aeval (rationalCoordinate (K := K) (n := 4)) (E.symm P) := by
    change _ = aeval (rationalCoordinate (K := K) (n := 4)) (rename s.symm P)
    rw [aeval_rename]
    rfl
  have hdiv : E G ∣ P ↔ G ∣ E.symm P := by
    constructor
    · intro h
      simpa only [AlgEquiv.symm_apply_apply] using map_dvd E.symm h
    · intro h
      simpa only [AlgEquiv.apply_symm_apply] using map_dvd E h
  change aeval (fun j => rationalCoordinate (K := K) (s.symm j)) P = 0 ↔ _
  rw [heval, Ideal.mem_span_singleton]
  have he : aeval (rationalCoordinate (K := K) (n := 4)) (E.symm P) = 0 ↔ G ∣ E.symm P := by
    change E.symm P ∈ fiberVanishingIdeal (L := C) (rationalCoordinate (K := K) (n := 4)) ↔ _
    rw [actual_closed_gauss_pencil_relation_ideal H I e p q hq hrel ht, Ideal.mem_span_singleton]
  exact he.trans hdiv.symm

/-- Every chosen projective source chart has precisely the dehomogenized
pencil equation as its full original-source relation ideal. -/
theorem actual_closed_gauss_pencil_chart_relation_ideal
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (p q : R) {D : ℕ}
    (hq : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X = algebraMap R F p / algebraMap R F q)
    (s : Fin 4 ≃ Option (Fin 3)) :
    fiberVanishingIdeal (L := closedGaussParameterField H I) (closedGaussPencilChartPoint (K := K) s) =
      Ideal.span {closedGaussPencilChartEquation H I e p q s} := by
  have hx : rationalCoordinate (K := K) (s.symm none) ≠ 0 := by
    simpa only [rationalCoordinate, map_zero] using
      (IsFractionRing.injective R F).ne (X_ne_zero (s.symm none))
  exact homogeneous_principal_source_chart_relation_ideal
    (C := closedGaussParameterField H I)
    (fun j => rationalCoordinate (K := K) (s.symm j)) hx
    (rename s (closedGaussPencilEquation H I e p q))
    ((actual_closed_gauss_pencil_homogeneous_degree H I e p q hq hrel hpH hqH).2.1.rename_isHomogeneous)
    (actual_closed_gauss_pencil_reindexed_relation_ideal H I e p q hq hrel ht s)

/-- The actual projective pencil chart coordinate algebra in the source. -/
noncomputable def closedGaussPencilChartAlgebra
    (H : Fin 4 → R) (I : ImageRelationWitness H) (s : Fin 4 ≃ Option (Fin 3)) :
    Subalgebra (closedGaussParameterField H I) F :=
  fiberCoordinateAlgebra (L := closedGaussParameterField H I) (closedGaussPencilChartPoint (K := K) s)

/-- The affine equation quotient is exactly the actual chart coordinate
algebra, so its finite normalization belongs to the original pencil. -/
noncomputable def closedGaussPencilChartCoordinateEquiv
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (p q : R) {D : ℕ}
    (hq : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X = algebraMap R F p / algebraMap R F q)
    (s : Fin 4 ≃ Option (Fin 3)) :
    (MvPolynomial (Fin 3) (closedGaussParameterField H I) ⧸
      Ideal.span {closedGaussPencilChartEquation H I e p q s}) ≃ₐ[closedGaussParameterField H I]
        closedGaussPencilChartAlgebra H I s := by
  rw [← actual_closed_gauss_pencil_chart_relation_ideal H I e p q hq hrel hpH hqH ht s]
  exact fiberCoordinateQuotientEquiv _

/-- The normalization of an actual projective pencil chart in its own
fraction field. -/
noncomputable def closedGaussPencilChartNormalization
    (H : Fin 4 → R) (I : ImageRelationWitness H) (s : Fin 4 ≃ Option (Fin 3)) :=
  normalizationRing (closedGaussPencilChartAlgebra H I s)

/-- The actual projective pencil chart is a finitely generated algebra
over the closed Gauss parameter field. -/
theorem closedGaussPencilChartAlgebra_finiteType
    (H : Fin 4 → R) (I : ImageRelationWitness H) (s : Fin 4 ≃ Option (Fin 3)) :
    Algebra.FiniteType (closedGaussParameterField H I) (closedGaussPencilChartAlgebra H I s) :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)

variable [CharZero K]

/-- Normalization is finite on each actual standard projective pencil chart. -/
theorem actual_closed_gauss_pencil_chart_normalization_finite
    (H : Fin 4 → R) (I : ImageRelationWitness H) (s : Fin 4 ≃ Option (Fin 3)) :
    Module.Finite (closedGaussPencilChartAlgebra H I s) (closedGaussPencilChartNormalization H I s) := by
  let : CharZero (closedGaussParameterField H I) :=
    charZero_of_injective_algebraMap (algebraMap K (closedGaussParameterField H I)).injective
  let : Algebra.FiniteType (closedGaussParameterField H I) (closedGaussPencilChartAlgebra H I s) :=
    closedGaussPencilChartAlgebra_finiteType H I s
  exact normalizationRing_finite _ (K := closedGaussParameterField H I)

omit [CharZero K] in
/-- Each actual normalized projective pencil chart is normal. -/
theorem actual_closed_gauss_pencil_chart_normalization_normal
    (H : Fin 4 → R) (I : ImageRelationWitness H) (s : Fin 4 ≃ Option (Fin 3)) :
    IsIntegrallyClosed (closedGaussPencilChartNormalization H I s) :=
  normalizationRing_isIntegrallyClosed _

omit [CharZero K] in
/-- Each actual normalized projective pencil chart is birational to its
original chart: the actual fraction field is unchanged. -/
theorem actual_closed_gauss_pencil_chart_normalization_fraction_field
    (H : Fin 4 → R) (I : ImageRelationWitness H) (s : Fin 4 ≃ Option (Fin 3)) :
    IsFractionRing (closedGaussPencilChartNormalization H I s)
      (FractionRing (closedGaussPencilChartAlgebra H I s)) :=
  normalizationRing_isFractionRing _

end DimensionFourDependence
