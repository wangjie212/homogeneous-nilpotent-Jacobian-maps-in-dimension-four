import DimensionFourDependence.AffineLineLeadingComponent
import DimensionFourDependence.AlgebraicDerivation

/-! # A rational planar direction with constant slope along its own lines -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2500000

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]

/-- If a derivation has `Dx=1`, `Dy=s` and `Ds=0`, an invariant
positive-degree binary polynomial has top homogeneous form vanishing
on `(1,s)`. Indeed `y-sx`, `s` and the value of the polynomial lie
in the constant field, over which `x` is transcendental. -/
theorem invariant_planar_line_direction_annihilates_top_component
    (D : Derivation K F F) (x y s : F)
    (hx : D x = 1) (hy : D y = s) (hs : D s = 0)
    (p : MvPolynomial (Fin 2) K) (hp : 0 < p.totalDegree)
    (hval : D (aeval ![x, y] p) = 0) :
    aeval ![(1 : F), s] (homogeneousComponent p.totalDegree p) = 0 := by
  let E := derivationConstants D
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  have hb : D (y - s * x) = 0 := by
    rw [map_sub, hy, D.leibniz, hx, hs]
    simp [smul_eq_mul]
  let b : E := ⟨y - s * x, hb⟩
  let slope : E := ⟨s, hs⟩
  let a : E := ⟨aeval ![x,y] p, hval⟩
  have htrans : Transcendental E x := by
    intro he
    have hz := derivation_zero_of_isAlgebraic (derivationOverConstantSubfield D E le_rfl) x he
    change D x = 0 at hz
    exact one_ne_zero (hx.symm.trans hz)
  let v : Fin 2 → Polynomial E := ![Polynomial.X, Polynomial.C b + Polynomial.C slope * Polynomial.X]
  let e : Polynomial E →ₐ[K] F := (Polynomial.aeval x : Polynomial E →ₐ[E] F).restrictScalars K
  have hv : (fun i => e (v i)) = ![x,y] := by
    funext i
    fin_cases i
    · simp [e, v]
    · change Polynomial.aeval x (Polynomial.C b + Polynomial.C slope * Polynomial.X) = y
      simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      change y - s * x + s * x = y
      exact sub_add_cancel y (s * x)
  have hline : (aeval v p : Polynomial E) = Polynomial.C a := by
    apply (transcendental_iff_injective.mp htrans)
    change e (aeval v p) = Polynomial.aeval x (Polynomial.C a)
    rw [comp_aeval_apply, hv, Polynomial.aeval_C]
    rfl
  have hcoeff := congrArg (fun w : Polynomial E => w.coeff p.totalDegree) hline
  rw [Polynomial.coeff_C, if_neg (Nat.ne_of_gt hp)] at hcoeff
  have htop : aeval ![(1 : E), slope] (homogeneousComponent p.totalDegree p) = 0 := by
    have h := affine_line_coefficient_at_totalDegree p (![0, b] : Fin 2 → E) ![1,slope]
    have hv' : (fun i : Fin 2 => Polynomial.C (![0,b] i) + Polynomial.C (![1,slope] i) * Polynomial.X) = v := by
      funext i
      fin_cases i <;> simp [v]
    rw [hv', hcoeff] at h
    exact h.symm
  have hm := congrArg E.val htop
  rw [comp_aeval_apply, map_zero] at hm
  have he : (fun i : Fin 2 => E.val ((![1,slope] : Fin 2 → E) i)) = ![1,s] := by
    funext i
    fin_cases i <;> rfl
  rwa [he] at hm

end DimensionFourDependence
