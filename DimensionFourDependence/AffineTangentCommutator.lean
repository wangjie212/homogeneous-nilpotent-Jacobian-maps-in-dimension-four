import DimensionFourDependence.AffineConeVertexDifferential

/-! # Affine triangular tangent lifts and their commutator

The vertex coefficients are affine in x,z and independent of w. The
commutator of the normalized x and z lifts is a constant vertex partial.
A common invariant with nonzero vertex derivative therefore forces the
one-form coefficients to be closed.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]

/-- The full affine vertical coefficient in the two transverse variables. -/
noncomputable def affineTangentVerticalCoefficient (b : Fin 3 → K) : MvPolynomial (Fin 3) K :=
  C (b 0) + C (b 1) * X 0 + C (b 2) * X 1

/-- The normalized lift of the x partial. -/
noncomputable def affineTangentLiftX (b : Fin 3 → K) :
    Derivation K (MvPolynomial (Fin 3) K) (MvPolynomial (Fin 3) K) :=
  pderiv 0 + affineTangentVerticalCoefficient b • pderiv 2

/-- The normalized lift of the z partial. -/
noncomputable def affineTangentLiftZ (c : Fin 3 → K) :
    Derivation K (MvPolynomial (Fin 3) K) (MvPolynomial (Fin 3) K) :=
  pderiv 1 + affineTangentVerticalCoefficient c • pderiv 2

/-- The lift acts on every original affine polynomial by the actual
horizontal and vertical partials. -/
theorem affineTangentLiftX_apply (b : Fin 3 → K) (P : MvPolynomial (Fin 3) K) :
    affineTangentLiftX b P = pderiv 0 P + affineTangentVerticalCoefficient b * pderiv 2 P := by
  simp only [affineTangentLiftX, Derivation.add_apply, Derivation.smul_apply, smul_eq_mul]

/-- The z lift acts by its actual two original polynomial partials. -/
theorem affineTangentLiftZ_apply (c : Fin 3 → K) (P : MvPolynomial (Fin 3) K) :
    affineTangentLiftZ c P = pderiv 1 P + affineTangentVerticalCoefficient c * pderiv 2 P := by
  simp only [affineTangentLiftZ, Derivation.add_apply, Derivation.smul_apply, smul_eq_mul]

/-- Every partial of an affine vertical coefficient, including its
vanishing original vertex partial. -/
theorem affineTangentVerticalCoefficient_pderiv (b : Fin 3 → K) (i : Fin 3) :
    pderiv i (affineTangentVerticalCoefficient b) = (![C (b 1), C (b 2), 0] : Fin 3 → MvPolynomial (Fin 3) K) i := by
  fin_cases i <;> simp [affineTangentVerticalCoefficient, Derivation.leibniz, smul_eq_mul]

/-- The normalized affine lifts have precisely this constant vertical
commutator as an equality of original polynomial derivations. -/
theorem affine_tangent_lifts_commutator (b c : Fin 3 → K) :
    ⁅affineTangentLiftX b, affineTangentLiftZ c⁆ = (C (c 1 - b 2) : MvPolynomial (Fin 3) K) • pderiv (2 : Fin 3) := by
  apply MvPolynomial.derivation_ext
  intro i
  fin_cases i <;>
    simp [Derivation.commutator_apply, affineTangentLiftX_apply, affineTangentLiftZ_apply,
      affineTangentVerticalCoefficient_pderiv, Derivation.smul_apply, smul_eq_mul]

/-- A common actual invariant with P_w nonzero forces the two affine
vertical coefficients to be a closed one-form. -/
theorem invariant_affine_tangent_lifts_closed
    (P : MvPolynomial (Fin 3) K) (hPw : pderiv (2 : Fin 3) P ≠ 0)
    (b c : Fin 3 → K) (hx : affineTangentLiftX b P = 0) (hz : affineTangentLiftZ c P = 0) :
    b 2 = c 1 := by
  have he := congrArg (fun D : Derivation K (MvPolynomial (Fin 3) K) (MvPolynomial (Fin 3) K) => D P)
    (affine_tangent_lifts_commutator b c)
  simp only [Derivation.commutator_apply, hx, hz, map_zero, sub_self,
    Derivation.smul_apply, smul_eq_mul] at he
  have hc : C (c 1 - b 2) = (0 : MvPolynomial (Fin 3) K) :=
    (mul_eq_zero.mp he.symm).resolve_right hPw
  have hcoef : c 1 - b 2 = 0 := by
    apply MvPolynomial.C_injective (Fin 3) K
    simpa only [map_zero] using hc
  exact (sub_eq_zero.mp hcoef).symm

end DimensionFourDependence
