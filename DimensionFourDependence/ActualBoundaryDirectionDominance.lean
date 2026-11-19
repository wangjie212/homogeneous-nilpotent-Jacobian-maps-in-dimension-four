import DimensionFourDependence.ActualBoundaryTargetGeneric

/-! # The actual fiber boundary and the dominant-restriction obstruction

Actual closure membership supplies the primitive cross equations and
the original target genericity. A generic source direction therefore
constructs projective dominance. Equality of its original Gauss parameter
with the target then contradicts the proved Lemma 4.3.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "x" => rationalCoordinate (K := K) (n := 4)
local notation "y₀" => actualChartOutputCoordinate H hrank p hY

include hY

/-- Every actual full-fiber closure point satisfies the primitive-map
cross equations over the original coefficients. All coefficient maps
and the actual fiber evaluation are derived from the original map. -/
theorem actual_full_fiber_closure_primitive_cross_equations
    (g : MvPolynomial (Fin 4) K) (P : Fin 4 → MvPolynomial (Fin 4) K)
    {D : ℕ} (hP : IsHomogMap P D) (hHP : H = fun i => g * P i)
    (κ : Type u) [Field κ] [Algebra (L) κ] [Algebra K κ] [IsScalarTower K (L) κ]
    (z : Option (Fin 4) → κ) (hz : z ≠ 0)
    (hboundary : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (x)) :
    ∀ i j, algebraMap (L) κ ((y₀) i) * aeval (fun k => z (some k)) (P j) -
      algebraMap (L) κ ((y₀) j) * aeval (fun k => z (some k)) (P i) = 0 := by
  have he := primitive_boundary_cross_equations
    (fun i => MvPolynomial.map (algebraMap K (L)) (H i))
    (fun i => MvPolynomial.map (algebraMap K (L)) (P i)) (MvPolynomial.map (algebraMap K (L)) g)
    (fun i => (hP i).map (algebraMap K (L)))
    (by funext i; rw [congrFun hHP i, map_mul]) (x) (y₀)
    (actualChartOutputCoordinate_ne_zero H hrank p hY)
    (actualChartOutputCoordinate_fiber_evaluation H hrank p hY) z hz hboundary
  intro i j
  simpa only [aeval_map_algebra_extension] using he i j

/-- A generic actual boundary source direction constructs a dominant
restriction of the original primitive part. No cross equations, target
genericity, nonzero primitive value or scalar comparison is supplied. -/
theorem actual_full_fiber_boundary_generic_direction_implies_dominance
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hH0 : H ≠ 0) (I : ImageRelationWitness H)
    (g : MvPolynomial (Fin 4) K) (P : Fin 4 → MvPolynomial (Fin 4) K)
    {D : ℕ} (hD : 0 < D) (hP : IsHomogMap P D) (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (κ : Type u) [Field κ] [Algebra (L) κ] [Algebra K κ] [IsScalarTower K (L) κ]
    (z : Option (Fin 4) → κ) (hz : z ≠ 0) (hb : (fun i => z (some i)) ≠ 0)
    (hboundary : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (x))
    (hgeneric : projectiveFieldPoint (E := K) (fun i => z (some i)) hb = projectiveImageGenericPoint H hd hH hH0) :
    originalProjectiveRestrictionDominant H hd hH hH0 hrank I P hD hP hprim :=
  actual_boundary_generic_source_constructs_dominant_restriction H hrank p hY hd hH hH0 I P hD hP hprim
    κ (fun i => z (some i)) hb hgeneric
    (actual_full_fiber_closure_primitive_cross_equations H hrank p hY g P hP hHP κ z hz hboundary)

/-- An actual full-fiber boundary direction with the target's original
Gauss-parameter value cannot be generic on the original image. The
remaining parameter comparison is stated explicitly; its derivation
from the actual ruling and the boundary-incidence descent is separate. -/
theorem actual_full_fiber_boundary_not_generic_of_parameter_comparison
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hH0 : H ≠ 0)
    (hN : IsNilpotent (jac H)) (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (g : MvPolynomial (Fin 4) K) (hg : g ≠ 0) (P : Fin 4 → MvPolynomial (Fin 4) K)
    {D : ℕ} (hD : 0 < D) (hP : IsHomogMap P D) (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (κ : Type u) [Field κ] [Algebra (L) κ] [Algebra K κ] [IsScalarTower K (L) κ]
    (z : Option (Fin 4) → κ) (hz : z ≠ 0) (hb : (fun i => z (some i)) ≠ 0)
    (hboundary : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (x))
    (r s : MvPolynomial (Fin 4) K) {m : ℕ} (hr : r.IsHomogeneous m) (hs : s.IsHomogeneous m)
    (hscone : algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField s ≠ 0)
    (ht : imageConeGaussHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField r /
        algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField s)
    (hcompare : aeval (fun i => z (some i)) r / aeval (fun i => z (some i)) s =
      aeval (fun i => algebraMap (L) κ ((y₀) i)) r / aeval (fun i => algebraMap (L) κ ((y₀) i)) s) :
    projectiveFieldPoint (E := K) (fun i => z (some i)) hb ≠ projectiveImageGenericPoint H hd hH hH0 := by
  intro hgeneric
  have hy := actualChartOutputCoordinate_extended_ne_zero H hrank p hY κ
  have hygen := actual_boundary_target_projective_generic H hrank p hY hd hH hH0 κ hy
  have hPb := primitive_part_defined_at_projective_generic_point H hd hH hH0 hrank I P hP hprim
    (fun i => z (some i)) hb hgeneric
  obtain ⟨c, hc, hby⟩ := nonzero_vectors_proportional_of_cross_equations _ _ hy hPb
    (actual_full_fiber_closure_primitive_cross_equations H hrank p hY g P hP hHP κ z hz hboundary)
  exact no_generic_original_direction_with_same_parameter_target H hd hH hH0 hN hind hrank I e g hg P
    hD hP hprim hHP _ _ hb hy hgeneric hygen c hc hby r s hr hs hscone ht hcompare

end DimensionFourDependence
