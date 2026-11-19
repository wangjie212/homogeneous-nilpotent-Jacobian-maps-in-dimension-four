import DimensionFourDependence.SegreGenericRulingExclusion
import DimensionFourDependence.ActualBoundaryTargetGeneric
import DimensionFourDependence.SegreOriginalOutputChart

/-! # Actual Segre boundary points on either ruling are nongeneric -/

namespace DimensionFourDependence

open MvPolynomial
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option quotPrecheck false

universe u
variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i.castSucc)))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y₀" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)
local notation "L₀" => coefficientField (K := K) (Y₀)
local notation "y₀" => actualChartOutputCoordinate H hrank (Equiv.refl (Fin 4)) hY
local notation "x₀" => rationalCoordinate (K := K) (n := 4)

include hY

/-- The actual full-fiber closure equations supply all primitive-map
target cross equations. On either original Segre ruling these equations
and Lemma 5.2 exclude the original image generic point. -/
theorem actual_full_fiber_segre_boundary_on_ruling_not_generic
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hH0 : H ≠ 0)
    (hN : IsNilpotent (jac H)) (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (G : MvPolynomial (Fin 4) K) (hG : G ≠ 0) (c : ℕ) (hGh : G.IsHomogeneous c)
    (P : Fin 4 → MvPolynomial (Fin 4) K) {m : ℕ} (hm : 0 < m) (hP : IsHomogMap P m)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => G * P i) (hcm : c + m = d)
    (κ : Type u) [Field κ] [Algebra (L₀) κ] [Algebra K κ] [IsScalarTower K (L₀) κ]
    (z : Option (Fin 4) → κ) (hz : z ≠ 0) (hb : (fun i => z (some i)) ≠ 0)
    (hboundary : projectiveFieldPoint (E := L₀) z hz ∈ projectiveClosureSet (L := L₀) (x₀))
    (r : Fin 4) (hr : r = 1 ∨ r = 2)
    (hruling : algebraMap (L₀) κ ((y₀) 0) * z (some r) -
      algebraMap (L₀) κ ((y₀) r) * z (some 0) = 0) :
    projectiveFieldPoint (E := K) (fun i => z (some i)) hb ≠ projectiveImageGenericPoint H hd hH hH0 := by
  intro hgeneric
  have hext := primitive_boundary_cross_equations
    (fun i => MvPolynomial.map (algebraMap K (L₀)) (H i))
    (fun i => MvPolynomial.map (algebraMap K (L₀)) (P i))
    (MvPolynomial.map (algebraMap K (L₀)) G) (fun i => (hP i).map (algebraMap K (L₀)))
    (by funext i; rw [congrFun hHP i, map_mul]) (x₀) (y₀)
    (actualChartOutputCoordinate_ne_zero H hrank (Equiv.refl (Fin 4)) hY)
    (actualChartOutputCoordinate_fiber_evaluation H hrank (Equiv.refl (Fin 4)) hY) z hz hboundary
  have hcross (i j : Fin 4) : algebraMap (L₀) κ ((y₀) i) * aeval (fun l => z (some l)) (P j) -
      algebraMap (L₀) κ ((y₀) j) * aeval (fun l => z (some l)) (P i) = 0 := by
    simpa only [aeval_map_algebra_extension] using hext i j
  letI : Algebra (coefficientField (K := K) (fun i : Fin 3 =>
      algebraMap (MvPolynomial (Fin 4) K) S₀ (H ((Equiv.refl (Fin 4)) i.castSucc)))) κ :=
    inferInstanceAs (Algebra (L₀) κ)
  letI : IsScalarTower K (coefficientField (K := K) (fun i : Fin 3 =>
      algebraMap (MvPolynomial (Fin 4) K) S₀ (H ((Equiv.refl (Fin 4)) i.castSucc)))) κ :=
    inferInstanceAs (IsScalarTower K (L₀) κ)
  have hy := actualChartOutputCoordinate_extended_ne_zero H hrank (Equiv.refl (Fin 4)) hY κ
  have hygen := actual_boundary_target_projective_generic H hrank (Equiv.refl (Fin 4)) hY hd hH hH0 κ hy
  exact no_generic_original_segre_direction_with_same_ruling_target H hd hH hN hrank hind I hSegre hH0
    G hG c hGh P hm hP hprim hHP hcm (fun i => z (some i))
    (fun i => algebraMap (L₀) κ ((y₀) i)) hb hy hgeneric hygen hcross r hr hruling

/-- The original map constructs its primitive homogeneous factorization
and thereby excludes genericity at every actual full-fiber boundary
direction preserving either original Segre ruling. -/
theorem original_segre_full_boundary_ruling_genericity_exclusion
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (κ : Type u) [Field κ] [Algebra (L₀) κ] [Algebra K κ] [IsScalarTower K (L₀) κ]
    (z : Option (Fin 4) → κ) (hz : z ≠ 0) (hb : (fun i => z (some i)) ≠ 0)
    (hboundary : projectiveFieldPoint (E := L₀) z hz ∈ projectiveClosureSet (L := L₀) (x₀))
    (r : Fin 4) (hr : r = 1 ∨ r = 2)
    (hruling : algebraMap (L₀) κ ((y₀) 0) * z (some r) -
      algebraMap (L₀) κ ((y₀) r) * z (some 0) = 0) :
    projectiveFieldPoint (E := K) (fun i => z (some i)) hb ≠
      projectiveImageGenericPoint H hd hH (rank_three_polynomial_map_ne_zero H hrank) := by
  obtain ⟨G, P, c, hc, hG, hGh, hP, hprim, hHP, hdeg⟩ :=
    exists_primitive_factorization_common_degree_le_sub_two H hH hind I
  exact actual_full_fiber_segre_boundary_on_ruling_not_generic H hrank hY hd hH
    (rank_three_polynomial_map_ne_zero H hrank) hN hind I hSegre G hG c hGh P (by omega)
    hP hprim hHP (Nat.add_sub_of_le (hc.trans (Nat.sub_le d 2))) κ z hz hb hboundary r hr hruling

end DimensionFourDependence
