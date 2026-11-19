/- Foundation adapted from the neighboring quartic project.
   Only the general-degree algebraic results are used for the present paper.
   The source theorem file with its admitted surface argument is not imported. -/
import Mathlib

/-!
# Linear dependence for homogeneous quartic maps with nilpotent Jacobian — definitions

This file contains the basic definitions used in the formalization of
*J. Wang and D. Yan, "Linear dependence for homogeneous quartic maps with nilpotent
Jacobian"* (the uploaded file `quartic_dependence.pdf`).  The conventions follow
§2.1 ("Conventions and background") of that paper.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- The Jacobian matrix of a polynomial map, with the convention
`(JH)ᵢⱼ = ∂Hᵢ/∂xⱼ` fixed in §2.1 ("Conventions and background") of `quartic_dependence.pdf`.
This is the matrix written `JH` in Theorem 1.1 and throughout the paper. -/
noncomputable def jac (H : Fin n → MvPolynomial (Fin n) K) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) K) :=
  Matrix.of fun i j => pderiv j (H i)

/-- The vector of coordinates `X = (x₁, …, xₙ)ᵀ` (introduced in §1 of `quartic_dependence.pdf`,
just before Theorem 1.1). -/
noncomputable def coordVec : Fin n → MvPolynomial (Fin n) K := fun i => X i

/-- The rank of a polynomial matrix, taken over the field of rational functions `K(X)`,
as stipulated in §2.1 of `quartic_dependence.pdf` ("Unless another field is specified,
ranks and kernels are taken over `K(X)`"). -/
noncomputable def polyRank {σ : Type*} (M : Matrix (Fin n) (Fin n) (MvPolynomial σ K)) : ℕ :=
  (M.map (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)))).rank

/-- A polynomial map all of whose components are homogeneous of degree `d`
(the hypothesis "homogeneous of degree four" of Theorem 1.1 of `quartic_dependence.pdf`,
for `d = 4`). -/
def IsHomogMap {σ : Type*} (H : Fin n → MvPolynomial σ K) (d : ℕ) : Prop :=
  ∀ i, (H i).IsHomogeneous d

/-- The components of `H` are linearly dependent over `K`: there is a nonzero
`λ ∈ Kⁿ` with `λ₁H₁ + ⋯ + λₙHₙ = 0`.  This is the conclusion of Theorem 1.1 of
`quartic_dependence.pdf`. -/
def ComponentsDependent {σ : Type*} (H : Fin n → MvPolynomial σ K) : Prop :=
  ∃ c : Fin n → K, c ≠ 0 ∧ ∑ i, c i • H i = 0

/-- A polynomial vector is *primitive* if the greatest common divisor of its components is
one, i.e. every common divisor is a unit (§2.1 of `quartic_dependence.pdf`). -/
def IsPrimitiveVec {σ : Type*} (u : Fin n → MvPolynomial σ K) : Prop :=
  ∀ p : MvPolynomial σ K, (∀ i, p ∣ u i) → IsUnit p

/-- `u` is a primitive homogeneous generator of degree `α` of the right kernel of `N`
(`N u = 0`), as in §2.1 and §1.2 of `quartic_dependence.pdf` ("primitive right normal"). -/
structure IsPrimRightKernel {σ : Type*} (N : Matrix (Fin n) (Fin n) (MvPolynomial σ K))
    (u : Fin n → MvPolynomial σ K) (α : ℕ) : Prop where
  ne_zero : u ≠ 0
  homog : IsHomogMap u α
  prim : IsPrimitiveVec u
  ker : N *ᵥ u = 0

/-- `v` is a primitive homogeneous generator of degree `β` of the left kernel of `N`
(`vᵀ N = 0`), the "primitive left normal" of §1.2 and §2.1 of `quartic_dependence.pdf`. -/
structure IsPrimLeftKernel {σ : Type*} (N : Matrix (Fin n) (Fin n) (MvPolynomial σ K))
    (v : Fin n → MvPolynomial σ K) (β : ℕ) : Prop where
  ne_zero : v ≠ 0
  homog : IsHomogMap v β
  prim : IsPrimitiveVec v
  ker : v ᵥ* N = 0

end DimensionFourDependence
