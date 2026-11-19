import DimensionFourDependence.TernaryLineSlopeTrace
import DimensionFourDependence.DerivationInvariantPlanarLine
import DimensionFourDependence.PlanarBinarySlopeAlgebraicity
import DimensionFourDependence.RationalJacobianCriterion

/-! # An invariant line's slope is algebraic over its fixed source coordinate -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 2000000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)
local notation "x" => (rationalCoordinate (K := K) (n := 3))
local notation "∂" => (rationalPartial (K := K) (n := 3))

attribute [local instance] MvPolynomial.algebraMvPolynomial

omit [CharZero K] in
private theorem adjoin_fixed_coordinate_le_derivationConstants
    (D : Derivation K F F) (hD : D (x 0) = 0) :
    IntermediateField.adjoin K {x 0} ≤ derivationConstants D :=
  IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hD)

/-- A rank-two family with an invariant line of direction `(0,s,1)`
has slope algebraic over the fixed rational coordinate. The invariant
binary polynomial is constructed from an actual output. -/
theorem invariant_ternary_line_slope_isAlgebraic_over_fixed_coordinate
    (H : Fin 3 → R₃) (hR : polyRank (jac H) = 2) (s : F)
    (hD : ∀ i, ternaryLineSlopeDerivation s (ι (H i)) = 0)
    (hs : ternaryLineSlopeDerivation s s = 0) :
    IsAlgebraic (IntermediateField.adjoin K {x 0}) s := by
  let D := ternaryLineSlopeDerivation (K := K) s
  have hx : D (x 0) = 0 := by
    simp [D, ternaryLineSlopeDerivation, Derivation.smul_apply, rationalPartial_coordinate]
  let B := IntermediateField.adjoin K {x 0}
  let : CharZero B := charZero_of_injective_algebraMap (algebraMap K B).injective
  let D' := derivationOverConstantSubfield D B (adjoin_fixed_coordinate_le_derivationConstants D hx)
  let t : B := ⟨x 0, IntermediateField.subset_adjoin K _ rfl⟩
  let g : R₃ →ₐ[K] MvPolynomial (Fin 2) B :=
    aeval (![C t, X 1, X 0] : Fin 3 → MvPolynomial (Fin 2) B)
  let ev : MvPolynomial (Fin 2) B →ₐ[K] F :=
    (aeval (![x 2, x 1] : Fin 2 → F) : MvPolynomial (Fin 2) B →ₐ[B] F).restrictScalars K
  have he : ev.comp g = IsScalarTower.toAlgHom K R₃ F := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [ev, g, IntermediateField.algebraMap_apply, t, rationalCoordinate]
  have hval (i : Fin 3) : ev (g (H i)) = ι (H i) := AlgHom.congr_fun he _
  have hBdim : Algebra.trdeg K B = 1 := by
    let Y : Fin 1 → F := fun _ => x 0
    have hY : AlgebraicIndependent K Y :=
      rationalCoordinates_algebraicIndependent.comp (fun _ : Fin 1 => (0 : Fin 3))
        (fun _ _ _ => Subsingleton.elim _ _)
    have hRange : Set.range Y = {x 0} := by ext z; simp [Y]
    have hh := (rationalOutputEquiv Y hY).trdeg_eq
    rw [rationalSource_trdeg_eq, hRange] at hh
    exact hh.symm
  have hp : ∃ i, 0 < (g (H i)).totalDegree := by
    by_contra hdeg
    push Not at hdeg
    let Q : Fin 3 → F := fun i => ι (H i)
    let E := IntermediateField.adjoin K (Set.range Q)
    have hle : E ≤ B := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨i, rfl⟩
      have hC := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero (hdeg i))
      have hc := hval i
      rw [hC] at hc
      change aeval (![x 2, x 1] : Fin 2 → F) (C ((g (H i)).coeff 0)) = _ at hc
      rw [aeval_C] at hc
      change ι (H i) ∈ B
      rw [← hc]
      exact ((g (H i)).coeff 0).property
    let incl := IntermediateField.inclusion hle
    have htr := trdeg_le_of_injective incl incl.injective
    change Algebra.trdeg K E ≤ Algebra.trdeg K B at htr
    have hr : (rationalJacobian Q).rank = 2 := by
      rw [show rationalJacobian Q = _ from rationalJacobian_polynomial H]
      exact hR
    change Algebra.trdeg K (IntermediateField.adjoin K (Set.range Q)) ≤ _ at htr
    rw [rationalJacobian_rank_eq_output_trdeg Q, hr, hBdim] at htr
    norm_num at htr
  obtain ⟨i, hi⟩ := hp
  let P := g (H i)
  have hP : D' (aeval (![x 2, x 1] : Fin 2 → F) P) = 0 := by
    change D (ev (g (H i))) = 0
    rw [hval]
    exact hD i
  have h2 : D' (x 2) = 1 := by
    change D (x 2) = 1
    simp [D, ternaryLineSlopeDerivation, Derivation.smul_apply, rationalPartial_coordinate]
  have h1 : D' (x 1) = s := by
    change D (x 1) = s
    simp [D, ternaryLineSlopeDerivation, Derivation.smul_apply, rationalPartial_coordinate]
  have ht := invariant_planar_line_direction_annihilates_top_component D' (x 2) (x 1) s
    h2 h1 hs P hi hP
  have hP0 : P ≠ 0 := by
    change 0 < P.totalDegree at hi
    intro h
    rw [h, totalDegree_zero] at hi
    exact (Nat.lt_irrefl 0) hi
  exact slope_isAlgebraic_of_homogeneous_binary_form_zero _
    (top_homogeneousComponent_ne_zero P hP0)
    (homogeneousComponent_isHomogeneous _ _) s ht

/-- An invariant ternary line with the first coordinate fixed and
constant slope along that line forces dependence. -/
theorem invariant_ternary_line_with_fixed_first_coordinate_componentsDependent
    [IsAlgClosed K]
    (H : Fin 3 → R₃) (h0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (H i) = 0)
    (hN : IsNilpotent (jac H)) (hR : polyRank (jac H) = 2) (s : F)
    (hD : ∀ i, ternaryLineSlopeDerivation s (ι (H i)) = 0)
    (hs : ternaryLineSlopeDerivation s s = 0) :
    ComponentsDependent H := by
  let B := IntermediateField.adjoin K {x 0}
  let : CharZero B := charZero_of_injective_algebraMap (algebraMap K B).injective
  have ha := invariant_ternary_line_slope_isAlgebraic_over_fixed_coordinate H hR s hD hs
  have hkill (i : Fin 3) (hi : i ≠ 0) : ∂ i s = 0 := by
    have hp : ∂ i (x 0) = 0 := by rw [rationalPartial_coordinate, if_neg (Ne.symm hi)]
    let d := derivationOverConstantSubfield (∂ i) B (adjoin_fixed_coordinate_le_derivationConstants _ hp)
    exact derivation_zero_of_isAlgebraic d s ha
  exact invariant_ternary_line_with_fixed_coordinate_slope_componentsDependent H h0 hN s hD
    (hkill 1 (by decide)) (hkill 2 (by decide))

end DimensionFourDependence
