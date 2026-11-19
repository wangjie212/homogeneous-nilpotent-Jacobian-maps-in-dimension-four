import DimensionFourDependence.AffineConeTrace

/-! # The original affine trace in independent level coordinates

For P=w-Q(x,z), the substitution w=t+Q(x,z) takes the actual affine
trace to K[t][x,z]. It holds the parameter fixed while keeping every
scalar and mixed-coordinate coefficient polynomial.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]

/-- The actual level substitution (x,z,w)=(x,z,t+Q). -/
noncomputable def affineConeLevelSubstitution (Q : MvPolynomial (Fin 2) K) :
    MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 2) (Polynomial K) :=
  aeval ![X 0, X 1, C Polynomial.X + MvPolynomial.map Polynomial.C Q]

/-- Its values on all three original affine coordinates. -/
theorem affineConeLevelSubstitution_X (Q : MvPolynomial (Fin 2) K) (i : Fin 3) :
    affineConeLevelSubstitution Q (X i) =
      (![X 0, X 1, C Polynomial.X + MvPolynomial.map Polynomial.C Q] :
        Fin 3 → MvPolynomial (Fin 2) (Polynomial K)) i := by
  simp only [affineConeLevelSubstitution, aeval_X]

/-- Every original binary polynomial is unchanged except for the
canonical constant coefficient inclusion K into K[t]. -/
theorem affineConeLevelSubstitution_binary
    (Q q : MvPolynomial (Fin 2) K) :
    affineConeLevelSubstitution Q (rename Fin.castSucc q) = MvPolynomial.map Polynomial.C q := by
  induction q using MvPolynomial.induction_on with
  | C c =>
    rw [rename_C, MvPolynomial.map_C]
    exact (affineConeLevelSubstitution Q).commutes c
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, rename_X, hp, MvPolynomial.map_X]
    congr 1
    rw [affineConeLevelSubstitution_X]
    fin_cases i <;> rfl

/-- The whole parameter P=w-Q becomes the independent coefficient t. -/
theorem affineConeLevelSubstitution_parameter (Q : MvPolynomial (Fin 2) K) :
    affineConeLevelSubstitution Q (X 2 - rename Fin.castSucc Q) = C Polynomial.X := by
  rw [map_sub, affineConeLevelSubstitution_X, affineConeLevelSubstitution_binary]
  change C Polynomial.X + MvPolynomial.map Polynomial.C Q - MvPolynomial.map Polynomial.C Q = _
  exact add_sub_cancel_right _ _

/-- Every scalar polynomial in P is transported to exactly the same
polynomial in the independent coefficient parameter t. -/
theorem affineConeLevelSubstitution_scalar
    (Q : MvPolynomial (Fin 2) K) (A : Polynomial K) :
    affineConeLevelSubstitution Q (Polynomial.aeval (X 2 - rename Fin.castSucc Q) A) = C A := by
  rw [← Polynomial.aeval_algHom_apply, affineConeLevelSubstitution_parameter]
  induction A using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.aeval_monomial]
    change C (Polynomial.C a) * C Polynomial.X ^ n = C (Polynomial.monomial n a)
    rw [← map_pow, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial]

/-- The binary inclusion has no derivative in the omitted w coordinate. -/
theorem binary_rename_vertex_pderiv_zero (Q : MvPolynomial (Fin 2) K) :
    pderiv (2 : Fin 3) (rename Fin.castSucc Q) = 0 := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp only [rename_C, pderiv_C]
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p i hp =>
    simp only [map_mul, rename_X, Derivation.leibniz, smul_eq_mul, hp, mul_zero, add_zero]
    fin_cases i <;> simp

/-- The two transverse parameter partials become minus the partials of
Q over K[t], while its vertex partial becomes one. -/
theorem affineConeLevelSubstitution_parameter_partials
    (Q : MvPolynomial (Fin 2) K) :
    affineConeLevelSubstitution Q (pderiv (0 : Fin 3) (X 2 - rename Fin.castSucc Q)) =
        -pderiv (0 : Fin 2) (MvPolynomial.map Polynomial.C Q) ∧
    affineConeLevelSubstitution Q (pderiv (1 : Fin 3) (X 2 - rename Fin.castSucc Q)) =
        -pderiv (1 : Fin 2) (MvPolynomial.map Polynomial.C Q) ∧
    affineConeLevelSubstitution Q (pderiv (2 : Fin 3) (X 2 - rename Fin.castSucc Q)) = 1 := by
  have h0 : pderiv (0 : Fin 3) (rename Fin.castSucc Q) = rename Fin.castSucc (pderiv (0 : Fin 2) Q) :=
    pderiv_rename (Fin.castSucc_injective 2) (0 : Fin 2) Q
  have h1 : pderiv (1 : Fin 3) (rename Fin.castSucc Q) = rename Fin.castSucc (pderiv (1 : Fin 2) Q) :=
    pderiv_rename (Fin.castSucc_injective 2) (1 : Fin 2) Q
  simp only [map_sub, pderiv_X, Pi.single_apply, h0, h1, binary_rename_vertex_pderiv_zero,
    affineConeLevelSubstitution_binary, pderiv_map]
  norm_num

/-- The complete expression (4.11) in K[t][x,z]. -/
noncomputable def quadraticConeLevelTracePolynomial (d : ℕ)
    (Q : MvPolynomial (Fin 2) K) (A B : Fin 3 → Polynomial K) :
    MvPolynomial (Fin 2) (Polynomial K) :=
  C ((d : Polynomial K) * A 1 - Polynomial.X * (A 1).derivative) +
    C (A 1).derivative *
      (X 0 * pderiv 0 (MvPolynomial.map Polynomial.C Q) +
        X 1 * pderiv 1 (MvPolynomial.map Polynomial.C Q) - MvPolynomial.map Polynomial.C Q) -
    C (A 0).derivative * pderiv 0 (MvPolynomial.map Polynomial.C Q) -
    C (A 2).derivative * pderiv 1 (MvPolynomial.map Polynomial.C Q) +
    C (B 0).derivative * X 0 + C (B 1).derivative + C (B 2).derivative * X 1

/-- The actual affine trace transports to the entire independent-level
identity (4.11), without assuming any coefficient comparison. -/
theorem affine_cone_trace_transports_to_quadratic_level_identity
    (d : ℕ) (Q : MvPolynomial (Fin 2) K) (A B : Fin 3 → Polynomial K) :
    affineConeLevelSubstitution Q (affineConeTracePolynomial d (X 2 - rename Fin.castSucc Q) A B) =
      quadraticConeLevelTracePolynomial d Q A B := by
  have h0 : pderiv (0 : Fin 3) (rename Fin.castSucc Q) = rename Fin.castSucc (pderiv (0 : Fin 2) Q) :=
    pderiv_rename (Fin.castSucc_injective 2) (0 : Fin 2) Q
  have h1 : pderiv (1 : Fin 3) (rename Fin.castSucc Q) = rename Fin.castSucc (pderiv (1 : Fin 2) Q) :=
    pderiv_rename (Fin.castSucc_injective 2) (1 : Fin 2) Q
  have hder0 : pderiv (0 : Fin 3) (X 2 - rename Fin.castSucc Q) = -rename Fin.castSucc (pderiv (0 : Fin 2) Q) := by
    simp only [map_sub, pderiv_X, Pi.single_apply, h0]
    norm_num
  have hder1 : pderiv (1 : Fin 3) (X 2 - rename Fin.castSucc Q) = -rename Fin.castSucc (pderiv (1 : Fin 2) Q) := by
    simp only [map_sub, pderiv_X, Pi.single_apply, h1]
    norm_num
  have hder2 : pderiv (2 : Fin 3) (X 2 - rename Fin.castSucc Q) = 1 := by
    simp only [map_sub, pderiv_X, Pi.single_apply, binary_rename_vertex_pderiv_zero]
    norm_num
  dsimp only [affineConeTracePolynomial]
  rw [hder0, hder1, hder2]
  simp only [map_add, map_sub, map_mul, map_neg, map_one,
    affineConeLevelSubstitution_scalar, affineConeLevelSubstitution_X,
    affineConeLevelSubstitution_binary, ← pderiv_map,
    quadraticConeLevelTracePolynomial, map_sub, map_mul, map_natCast]
  dsimp
  ring

end DimensionFourDependence
