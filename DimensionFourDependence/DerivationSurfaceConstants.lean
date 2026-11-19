import DimensionFourDependence.AlgebraicDerivation
import DimensionFourDependence.CoefficientCurveField

/-! # Joint directional and Euler constants on a surface field -/

namespace DimensionFourDependence

universe u

variable {K F : Type u} [Field K] [CharZero K] [Field F] [Algebra K F]

/-- A direction with a coordinate of derivative one leaves at most a
one-dimensional constant field inside a field of dimension at most two. -/
theorem direction_constants_trdeg_le_one_on_surface
    (D : Derivation K F F) (r : F) (hr : D r = 1)
    (htr : Algebra.trdeg K F ≤ 2) :
    Algebra.trdeg K (derivationConstants D) ≤ 1 := by
  let C := derivationConstants D
  let : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  have hn : Algebra.trdeg C F ≠ 0 := by
    intro hz
    let : Algebra.IsAlgebraic C F := trdeg_eq_zero_iff.mp hz
    have he := derivation_zero_of_isAlgebraic
      (derivationOverConstantSubfield D C le_rfl) r (Algebra.IsAlgebraic.isAlgebraic r)
    change D r = 0 at he
    exact one_ne_zero (hr.symm.trans he)
  have hadd := trdeg_add_eq (A := F) K C
  have hle : Algebra.trdeg K C + 1 ≤ 2 := by
    calc
      _ ≤ Algebra.trdeg K C + Algebra.trdeg C F :=
        add_le_add le_rfl (Cardinal.one_le_iff_ne_zero.mpr hn)
      _ = Algebra.trdeg K F := hadd
      _ ≤ 2 := htr
  apply (Cardinal.add_one_le_add_one_iff (α := Algebra.trdeg K C) (β := 1)).mp
  simpa only [one_add_one_eq_two] using hle

/-- Euler differentiation preserves the constants of a direction when
their commutator is that direction. -/
noncomputable def eulerOnDirectionConstants (D E : Derivation K F F)
    (hcomm : ∀ x, D (E x) = E (D x) + D x) :
    Derivation K (derivationConstants D) (derivationConstants D) where
  toLinearMap :=
    { toFun := fun x => ⟨E x, by
        change D (E x) = 0
        rw [hcomm, x.property, map_zero, zero_add]⟩
      map_add' := by intros; apply Subtype.ext; exact map_add E _ _
      map_smul' := by
        intros
        apply Subtype.ext
        exact E.map_smul _ _ }
  map_one_eq_zero' := by apply Subtype.ext; exact E.map_one_eq_zero
  leibniz' := by intros; apply Subtype.ext; exact E.leibniz _ _

omit [CharZero K] in
theorem eulerOnDirectionConstants_value (D E : Derivation K F F)
    (hcomm : ∀ x, D (E x) = E (D x) + D x) (x : derivationConstants D) :
    (eulerOnDirectionConstants D E hcomm x : F) = E x := rfl

/-- On a surface, a direction coordinate and a nonzero transverse
Euler coordinate force their joint constants to be algebraic over the
original base field. No algebraic-closedness assumption is needed. -/
theorem joint_direction_euler_constants_isAlgebraic
    (D E : Derivation K F F) (r s : F) (hr : D r = 1) (hsD : D s = 0)
    (hsE : E s = s) (hs : s ≠ 0)
    (hcomm : ∀ x, D (E x) = E (D x) + D x)
    (htr : Algebra.trdeg K F ≤ 2) (x : F) (hxD : D x = 0) (hxE : E x = 0) :
    IsAlgebraic K x := by
  let C := derivationConstants D
  let Δ := eulerOnDirectionConstants D E hcomm
  have hΔ : Δ ≠ 0 := by
    intro hz
    have he := congrArg (fun δ : Derivation K C C => (δ ⟨s, hsD⟩ : F)) hz
    change E s = 0 at he
    exact hs (hsE.symm.trans he)
  have hx := (derivation_zero_iff_isAlgebraic_of_trdeg_le_one Δ hΔ
    (direction_constants_trdeg_le_one_on_surface D r hr htr) (⟨x, hxD⟩ : C)).mp
      (by apply Subtype.ext; exact hxE)
  exact hx.algHom C.val

end DimensionFourDependence
