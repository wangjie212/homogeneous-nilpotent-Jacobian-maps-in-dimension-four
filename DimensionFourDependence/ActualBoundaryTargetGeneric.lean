import DimensionFourDependence.ActualFullFiberBoundary
import DimensionFourDependence.PrimitiveBoundaryParameter

/-! # Actual boundary targets retain the original projective generic point

The original output constants preserve every original polynomial
relation after passage to a boundary residue field. Thus a generic
boundary source direction would make the primitive restriction dominant.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "y₀" => actualChartOutputCoordinate H hrank p hY

/-- Extending the actual output constants preserves the whole
original relation ideal, including inhomogeneous equations. -/
theorem actualChartOutputCoordinate_extended_relations
    (κ : Type u) [Field κ] [Algebra (L) κ] [Algebra K κ] [IsScalarTower K (L) κ]
    (R : MvPolynomial (Fin 4) K) :
    aeval (fun i => algebraMap (L) κ ((y₀) i)) R = 0 ↔ aeval H R = 0 := by
  have heκ := comp_aeval_apply (y₀) (IsScalarTower.toAlgHom K (L) κ) R
  have heS : algebraMap (L) S₀ (aeval (y₀) R) =
      algebraMap (MvPolynomial (Fin 4) K) S₀ (aeval H R) := by
    calc
      _ = aeval (fun i => algebraMap (L) S₀ ((y₀) i)) R :=
        comp_aeval_apply (y₀) (IsScalarTower.toAlgHom K (L) S₀) R
      _ = aeval (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) R := by
        rw [funext (actualChartOutputCoordinate_source H hrank p hY)]
      _ = _ := (aeval_polynomial_to_fraction H R).symm
  change algebraMap (L) κ (aeval (y₀) R) = aeval (fun i => algebraMap (L) κ ((y₀) i)) R at heκ
  rw [← heκ, map_eq_zero_iff _ (algebraMap (L) κ).injective]
  constructor
  · intro hz
    apply IsFractionRing.injective (MvPolynomial (Fin 4) K) S₀
    rw [map_zero, ← heS, hz, map_zero]
  · intro hz
    apply (algebraMap (L) S₀).injective
    rw [map_zero, heS, hz, map_zero]

/-- The actual original target remains nonzero in every compatible
extension of the coefficient field, including every boundary residue. -/
theorem actualChartOutputCoordinate_extended_ne_zero
    (κ : Type u) [Field κ] [Algebra (L) κ] :
    (fun i => algebraMap (L) κ ((y₀) i)) ≠ 0 := by
  intro hz
  apply actualChartOutputCoordinate_ne_zero H hrank p hY
  funext i
  apply (algebraMap (L) κ).injective
  simpa only [map_zero, Pi.zero_apply] using congrFun hz i

/-- Every actual boundary target represents the original projective
image generic point over the original field. Genericity is a conclusion. -/
theorem actual_boundary_target_projective_generic
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hH0 : H ≠ 0)
    (κ : Type u) [Field κ] [Algebra (L) κ] [Algebra K κ] [IsScalarTower K (L) κ]
    (hy : (fun i => algebraMap (L) κ ((y₀) i)) ≠ 0) :
    projectiveFieldPoint (E := K) (fun i => algebraMap (L) κ ((y₀) i)) hy =
      projectiveImageGenericPoint H hd hH hH0 := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro m R hR
  change R.IsHomogeneous m at hR
  rw [projectiveFieldPoint_homogeneous_mem _ hy R hR]
  exact actualChartOutputCoordinate_extended_relations H hrank p hY κ R

/-- The actual primitive-map cross equations make a generic boundary
source direction yield a dominant original projective restriction.
The scalar comparison, target genericity and regularity of P are derived. -/
theorem actual_boundary_generic_source_constructs_dominant_restriction
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hH0 : H ≠ 0) (I : ImageRelationWitness H)
    (P : Fin 4 → MvPolynomial (Fin 4) K) {D : ℕ} (hD : 0 < D)
    (hP : IsHomogMap P D) (hprim : IsPrimitiveVec P)
    (κ : Type u) [Field κ] [Algebra (L) κ] [Algebra K κ] [IsScalarTower K (L) κ]
    (b : Fin 4 → κ) (hb : b ≠ 0)
    (hbgen : projectiveFieldPoint (E := K) b hb = projectiveImageGenericPoint H hd hH hH0)
    (hcross : ∀ i j, algebraMap (L) κ ((y₀) i) * aeval b (P j) -
      algebraMap (L) κ ((y₀) j) * aeval b (P i) = 0) :
    originalProjectiveRestrictionDominant H hd hH hH0 hrank I P hD hP hprim := by
  have hy := actualChartOutputCoordinate_extended_ne_zero H hrank p hY κ
  have htarget := actual_boundary_target_projective_generic H hrank p hY hd hH hH0 κ hy
  have hPb := primitive_part_defined_at_projective_generic_point H hd hH hH0 hrank I P hP hprim b hb hbgen
  obtain ⟨c, hc, hby⟩ := nonzero_vectors_proportional_of_cross_equations _ _ hy hPb hcross
  exact generic_source_and_target_construct_projective_restriction_dominance H hd hH hH0 hrank I
    P hD hP hprim b _ hb hy hbgen htarget c hc hby

end DimensionFourDependence
