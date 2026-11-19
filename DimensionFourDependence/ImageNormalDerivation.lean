import DimensionFourDependence.ProjectiveImage

/-! # The image normal is constant along fibers and kills derived tangent directions

The normal is a polynomial in the outputs. Any derivation annihilating
the outputs therefore annihilates the normal. Differentiating its pairing
with the kernel direction shows that it annihilates every derived tangent
direction as well, as used in Proposition 2.3.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K A σ : Type*} [Field K] [CommRing A] [Algebra K A]

/-- A derivation annihilating each substituted coordinate kills every
polynomial in those coordinates. -/
theorem derivation_aeval_zero_of_coordinates (D : Derivation K A A) (x : σ → A)
    (hx : ∀ i, D (x i) = 0) (P : MvPolynomial σ K) : D (aeval x P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, D.leibniz, hp, hx, smul_zero, zero_add]

variable {F : Type*} [Field F] [Algebra K F] {n : ℕ}

/-- The product rule for a covector-direction pairing. -/
theorem derivation_dotProduct (D : Derivation K F F) (v u : Fin n → F) :
    D (v ⬝ᵥ u) = (fun i => D (v i)) ⬝ᵥ u + v ⬝ᵥ (fun i => D (u i)) := by
  simp only [dotProduct, map_sum, D.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- A constant normal killing a direction also kills its derivative. -/
theorem constant_normal_kills_derived_direction (D : Derivation K F F)
    (v u : Fin n → F) (hv : ∀ i, D (v i) = 0) (hu : v ⬝ᵥ u = 0) :
    v ⬝ᵥ (fun i => D (u i)) = 0 := by
  have he := congrArg D hu
  rw [derivation_dotProduct, map_zero] at he
  simpa only [hv, dotProduct, zero_mul, Finset.sum_const_zero, zero_add] using he

/-- A fiber-constant normal kills all iterated derivatives of a tangent direction. -/
theorem constant_normal_kills_iterated_directions (D : Derivation K F F)
    (v u : Fin n → F) (hv : ∀ i, D (v i) = 0) (hu : v ⬝ᵥ u = 0) (r : ℕ) :
    v ⬝ᵥ (fun i => ((D : F → F)^[r]) (u i)) = 0 := by
  induction r with
  | zero => simpa only [Function.iterate_zero, id_eq] using hu
  | succ r ih =>
    simpa only [Function.iterate_succ_apply'] using
      constant_normal_kills_derived_direction D v
        (fun i => ((D : F → F)^[r]) (u i)) hv ih

/-- The actual image normal is constant for every vertical derivation
of the source field; no separate constancy hypothesis is assumed. -/
theorem imageRelationNormal_vertical_constant
    (H : Fin n → MvPolynomial (Fin n) K) (R : MvPolynomial (Fin n) K)
    (D : Derivation K (FractionRing (MvPolynomial (Fin n) K))
      (FractionRing (MvPolynomial (Fin n) K)))
    (hDH : ∀ i, D (algebraMap (MvPolynomial (Fin n) K)
      (FractionRing (MvPolynomial (Fin n) K)) (H i)) = 0) (i : Fin n) :
    D (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
      (imageRelationNormal H R i)) = 0 := by
  change D (algebraMap _ _ (aeval H (pderiv i R))) = 0
  rw [aeval_polynomial_to_fraction]
  exact derivation_aeval_zero_of_coordinates D _ hDH _

/-- The actual image normal annihilates every iterated vertical
derivative of the right-kernel direction in the rank-three case. -/
theorem ImageRelationWitness.kernel_pairing_iterate
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) (W : ImageRelationWitness H)
    (u : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hu : (jac H).map (algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K))) *ᵥ u = 0)
    (D : Derivation K (FractionRing (MvPolynomial (Fin 4) K))
      (FractionRing (MvPolynomial (Fin 4) K)))
    (hDH : ∀ i, D (algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i)) = 0) (r : ℕ) :
    (fun i => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
      (imageRelationNormal H W.equation i)) ⬝ᵥ
      (fun i => ((D : FractionRing (MvPolynomial (Fin 4) K) →
        FractionRing (MvPolynomial (Fin 4) K))^[r]) (u i)) = 0 := by
  exact constant_normal_kills_iterated_directions D _ u
    (imageRelationNormal_vertical_constant H W.equation D hDH)
    (W.kernel_pairing H hN hrank u hu) r

end DimensionFourDependence
