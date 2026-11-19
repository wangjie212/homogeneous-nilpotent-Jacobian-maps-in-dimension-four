import DimensionFourDependence.CurvePoleValuation
import DimensionFourDependence.ValuationResidueCoordinates
import DimensionFourDependence.PrimitiveRationalVector
import Mathlib.RingTheory.Valuation.IsTrivialOn

/-! # The residue of a nontrivial curve valuation is algebraic over its constants

A transcendental residue would embed its entire rational-function field
inside the valuation ring. The curve dimension would then make a pole
algebraic over a field on which the valuation is trivial, a contradiction.
-/

namespace DimensionFourDependence

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

/-- Any rational-function-field realization has the field generated
by its actual parameter value as its entire field range. -/
theorem rational_function_algHom_fieldRange_eq_adjoin_parameter (f : RatFunc E →ₐ[E] F) :
    f.fieldRange = IntermediateField.adjoin E {f RatFunc.X} := by
  have he := congrArg (IntermediateField.map f) (RatFunc.adjoin_X (K := E))
  rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map] at he
  exact he.symm

variable (V : ValuationSubring F) [Algebra E V] [IsScalarTower E V F]

omit [Algebra E F] [IsScalarTower E (↥V) F] in
/-- A transcendental residue makes every nonzero polynomial in its
lift a unit of the actual valuation ring. -/
theorem residue_transcendental_polynomial_value_isUnit
    (y : V) (hy : Transcendental E (IsLocalRing.residue V y))
    (p : Polynomial E) (hp : p ≠ 0) : IsUnit (Polynomial.aeval y p) := by
  let π : V →ₐ[E] IsLocalRing.ResidueField V := IsScalarTower.toAlgHom E V _
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  change π (Polynomial.aeval y p) ≠ 0
  rw [← Polynomial.aeval_algHom_apply π y p]
  intro hz
  change Polynomial.aeval (IsLocalRing.residue V y) p = 0 at hz
  apply hp
  exact (transcendental_iff_injective.mp hy) (by simpa only [map_zero] using hz)

/-- In dimension at most one, a valuation with a pole has every
actual residue element algebraic over its original constant field. -/
theorem curve_valuation_residue_element_isAlgebraic
    (x : F) (hpole : 1 < V.valuation x) (htr : Algebra.trdeg E F ≤ 1) (y : V) :
    IsAlgebraic E (IsLocalRing.residue V y) := by
  by_contra hy
  have hUnits (p : nonZeroDivisors (Polynomial E)) : IsUnit (Polynomial.aeval y (p : Polynomial E)) :=
    residue_transcendental_polynomial_value_isUnit V y hy p
      (mem_nonZeroDivisors_iff_ne_zero.mp p.property)
  let ψ : RatFunc E →ₐ[E] V := IsLocalization.liftAlgHom hUnits
  have hψX : ψ RatFunc.X = y := by
    rw [← RatFunc.algebraMap_X]
    simp only [ψ, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    exact Polynomial.aeval_X y
  let f : RatFunc E →ₐ[E] F := (IsScalarTower.toAlgHom E V F).comp ψ
  have hfx : f RatFunc.X = (y : F) := by
    change algebraMap V F (ψ RatFunc.X) = (y : F)
    rw [hψX]
    rfl
  have hyF : Transcendental E (y : F) := by
    intro hyalg
    apply RatFunc.transcendental_X (K := E)
    exact (isAlgebraic_algHom_iff f f.injective).mp (by simpa only [hfx] using hyalg)
  let M := f.fieldRange
  have hM : M = IntermediateField.adjoin E {(y : F)} := by
    dsimp only [M]
    rw [rational_function_algHom_fieldRange_eq_adjoin_parameter f, hfx]
  have hMmem (a : M) : (a : F) ∈ V := by
    rcases a with ⟨a, r, rfl⟩
    exact (ψ r).property
  let : V.valuation.IsTrivialOn M := Valuation.IsTrivialOn.of_le_one V.valuation
    (fun a => (V.valuation_le_one_iff _).mpr (hMmem a))
  have hxalg : IsAlgebraic M x := by
    rw [hM]
    exact isAlgebraic_over_adjoin_of_trdeg_le_one htr (y : F) hyF x
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx, map_zero] at hpole
    exact (not_lt_of_ge zero_le_one) hpole
  exact (Valuation.transcendental_of_ne_one (v := V.valuation) M x hx0 (ne_of_gt hpole)) hxalg

/-- The whole residue field of a nontrivial curve valuation is
algebraic over the original constant field. No residue algebraicity,
closed point, discrete valuation or normalization is supplied. -/
theorem curve_valuation_residue_isAlgebraic
    (x : F) (hpole : 1 < V.valuation x) (htr : Algebra.trdeg E F ≤ 1) :
    Algebra.IsAlgebraic E (IsLocalRing.ResidueField V) := by
  constructor
  intro a
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective (R := V) a
  exact curve_valuation_residue_element_isAlgebraic V x hpole htr y

/-- A nonzero normalized boundary direction supplies its own
nontrivial valuation, so the curve dimension constructs residue
algebraicity without a separate pole hypothesis. -/
theorem normalized_curve_boundary_residue_isAlgebraic {n : ℕ}
    (x : Fin n → F) (i : Fin n) (s : F) (z : Option (Fin n) → V)
    (hz0 : (z none : F) = s) (hz : ∀ j, (z (some j) : F) = s * x j)
    (hr0 : IsLocalRing.residue V (z none) = 0)
    (hr1 : IsLocalRing.residue V (z (some i)) = 1)
    (htr : Algebra.trdeg E F ≤ 1) : Algebra.IsAlgebraic E (IsLocalRing.ResidueField V) := by
  have hs : s ≠ 0 := by
    intro hs
    have hzi : z (some i) = 0 := by
      apply Subtype.ext
      simpa only [hs, zero_mul, ZeroMemClass.coe_zero] using hz i
    have he := hr1
    rw [hzi, map_zero] at he
    exact zero_ne_one he
  have hvs : V.valuation s < 1 := by
    have he := (valuation_residue_zero_iff V (z none)).mp hr0
    rwa [hz0] at he
  have hpole : 1 < V.valuation s⁻¹ := by
    rw [map_inv₀]
    exact (one_lt_inv₀ (pos_iff_ne_zero.mpr ((map_ne_zero V.valuation).mpr hs))).mpr hvs
  exact curve_valuation_residue_isAlgebraic V s⁻¹ hpole htr

end DimensionFourDependence
