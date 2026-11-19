import DimensionFourDependence.TernaryGraphRelationIdeal
import DimensionFourDependence.TernaryGraphNonzeroHessian
import DimensionFourDependence.TernaryGraphInfinityValues
import DimensionFourDependence.TernaryHighestPartConstantPlanes
import DimensionFourDependence.ProjectiveSourceParameterField

/-! # The generic curve and its constant-plane cover in an independent chart -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u v
set_option maxHeartbeats 2300000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)
local notation "x" => (rationalCoordinate (K := K) (n := 3))

/-- The full relation ideal of the projected curve places all its
embedded directions at infinity in finitely many original constant planes. -/
theorem ternary_graph_generator_direction_cover
    (H : Fin 3 → R₃) (h0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (H i) = 0)
    (hind : ¬ComponentsDependent H) (hN : IsNilpotent (jac H))
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y)
    (hpair : ∀ i : Fin 2, Y i = ι (H i.castSucc))
    (w : coefficientField (K := K) Y) (hw : (w : F) = ι (H 2))
    (s : coefficientField (K := K) Y) (hs : (s : F) = ternaryGraphPlaneValue Y hY w)
    (P : MvPolynomial (Fin 2) (coefficientField (K := K) Y)) (hP : P ≠ 0)
    (hI : fiberVanishingIdeal (L := coefficientField (K := K) Y)
      (fun i : Fin 2 => x i.castSucc) = Ideal.span {P}) :
    ∃ C₀ : Finset (Fin 3 → K), (∀ l ∈ C₀, l ≠ 0) ∧
      ∀ (A : Type v) [Field A] [Algebra (coefficientField (K := K) Y) A]
        [Algebra K A] [IsScalarTower K (coefficientField (K := K) Y) A] (e : Fin 2 → A),
        aeval e (homogeneousComponent P.totalDegree P) = 0 →
          ∃ l ∈ C₀, aeval (![e 0, e 1,
            algebraMap (coefficientField (K := K) Y) A (coefficientPartial Y hY 0 w) * e 0 +
            algebraMap (coefficientField (K := K) Y) A (coefficientPartial Y hY 1 w) * e 1] : Fin 3 → A)
            (linearFormPolynomial l) = 0 := by
  let L := coefficientField (K := K) Y
  let : IsScalarTower K L F := coefficientFieldScalarTower Y
  have he : (![Y 0, Y 1, (w : F)] : Fin 3 → F) = fun i => ι (H i) := by
    funext i
    fin_cases i
    · exact hpair 0
    · exact hpair 1
    · exact hw
  obtain ⟨d, C₀, hd, hdeg, hC, hCover⟩ :=
    normalized_ternary_top_form_constructs_constant_planes H h0 hind hN
  refine ⟨C₀, hC, ?_⟩
  intro A _ _ _ _ e hzero
  let a := coefficientPartial Y hY 0 w
  let b := coefficientPartial Y hY 1 w
  let V : Fin 3 → L := ![algebraMap _ L (outputCoordinate (K := K) Y 0),
    algebraMap _ L (outputCoordinate (K := K) Y 1), w]
  have hV (i : Fin 3) : algebraMap L F (V i) = ι (H i) := by
    have hi : (![Y 0, Y 1, (w : F)] : Fin 3 → F) i = ι (H i) := congrFun he i
    exact (show algebraMap L F (V i) = (![Y 0, Y 1, (w : F)] : Fin 3 → F) i by
      fin_cases i <;> rfl).trans hi
  have hx : x = (![x 0, x 1,
      algebraMap L F s + algebraMap L F a * x 0 + algebraMap L F b * x 1] : Fin 3 → F) := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · change x 2 = (s : F) + ternaryGraphGradient Y hY w 0 * x 0 +
          ternaryGraphGradient Y hY w 1 * x 1
      change (s : F) = x 2 - ternaryGraphGradient Y hY w 0 * x 0 -
        ternaryGraphGradient Y hY w 1 * x 1 at hs
      linear_combination -hs
  have hc (i : Fin 3) : aeval (![x 0, x 1,
      algebraMap L F s + algebraMap L F a * x 0 + algebraMap L F b * x 1] : Fin 3 → F) (H i) =
      algebraMap L F (V i) := by
    rw [← hx, hV, rationalCoordinate_aeval]
  apply hCover A
  intro i
  exact ternary_graph_direction_annihilates_original_top a b s (V i)
    (fun j : Fin 2 => x j.castSucc) (H i) (hc i) P hP hI hd (hdeg i) e hzero

/-- The exact projected generic curve of a normalized independent
ternary map, including all its curve relations and the finite collection
of original constant planes covering its points at infinity. -/
theorem normalized_ternary_map_constructs_generic_curve
    (H : Fin 3 → R₃) (h0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (H i) = 0)
    (hind : ¬ComponentsDependent H) (hN : IsNilpotent (jac H))
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y)
    (hpair : ∀ i : Fin 2, Y i = ι (H i.castSucc))
    (w : coefficientField (K := K) Y) (hw : (w : F) = ι (H 2)) :
    ∃ (s τ : coefficientField (K := K) Y) (P : MvPolynomial (Fin 2) (coefficientField (K := K) Y))
      (C₀ : Finset (Fin 3 → K)),
      (s : F) = ternaryGraphPlaneValue Y hY w ∧
      (τ : F) = ternaryGraphQuadraticValue Y hY w s ∧
      fiberVanishingIdeal (L := coefficientField (K := K) Y) (fun i : Fin 2 => x i.castSucc) = Ideal.span {P} ∧
      Irreducible P ∧ (P.totalDegree = 1 ∨ P.totalDegree = 2) ∧
      P ∣ ternaryGraphQuadraticEquation Y hY w s τ ∧ (∀ l ∈ C₀, l ≠ 0) ∧
      ∀ (A : Type v) [Field A] [Algebra (coefficientField (K := K) Y) A]
        [Algebra K A] [IsScalarTower K (coefficientField (K := K) Y) A] (e : Fin 2 → A),
        aeval e (homogeneousComponent P.totalDegree P) = 0 →
          ∃ l ∈ C₀, aeval (![e 0, e 1,
            algebraMap (coefficientField (K := K) Y) A (coefficientPartial Y hY 0 w) * e 0 +
            algebraMap (coefficientField (K := K) Y) A (coefficientPartial Y hY 1 w) * e 1] : Fin 3 → A)
            (linearFormPolynomial l) = 0 := by
  have he : (![Y 0, Y 1, (w : F)] : Fin 3 → F) = fun i => ι (H i) := by
    funext i
    fin_cases i
    · exact hpair 0
    · exact hpair 1
    · exact hw
  have hn : IsNilpotent (rationalJacobian (![Y 0, Y 1, (w : F)] : Fin 3 → F)) := by
    rw [he, rationalJacobian_polynomial]
    exact hN.map (ι).mapMatrix
  obtain ⟨s, τ, hs, hτ⟩ := nilpotent_ternary_graph_constructs_plane_and_quadratic_values Y hY w hn
  have hHess := closed_field_normalized_ternary_graph_hessian_ne_zero H h0 hind Y hY hpair w hw
  obtain ⟨P, hI, hP, hdP, hdiv⟩ :=
    ternary_graph_relation_ideal_has_linear_or_quadratic_generator Y hY w s τ hs hτ hHess
  obtain ⟨C₀, hC, hCover⟩ := ternary_graph_generator_direction_cover.{u, v}
    H h0 hind hN Y hY hpair w hw s hs P hP.ne_zero hI
  exact ⟨s, τ, P, C₀, hs, hτ, hI, hP, hdP, hdiv, hC, hCover⟩

end DimensionFourDependence
