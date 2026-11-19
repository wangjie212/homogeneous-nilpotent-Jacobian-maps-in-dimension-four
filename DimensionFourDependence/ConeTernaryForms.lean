import DimensionFourDependence.ModifiedCubicFiberBoundary

/-! # The fixed-vertex cone form becomes explicit ternary forms

Replacing r by u times its tangent linear form in (4.7) constructs
the entire four original coordinate forms, including the last coordinate.
They are homogeneous of the original degree and retain their exact
values under every compatible coefficient-field realization.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {F : Type*} [Field F]

/-- The actual ternary forms obtained from the fixed-vertex cone
expression after substituting its tangent multiple for r. -/
noncomputable def coneTernaryForms
    (d : ℕ) (τ ν V : Fin 3 → F) (u a b : F) : Fin 4 → MvPolynomial (Fin 3) F :=
  Fin.snoc (fun i => C (V i) * (C u * linearFormPolynomial τ) ^ d)
    (C a * (C u * linearFormPolynomial τ) ^ d +
      C b * (C u * linearFormPolynomial τ) ^ (d - 1) * linearFormPolynomial ν)

theorem coneTernaryForms_castSucc (d : ℕ) (τ ν V : Fin 3 → F) (u a b : F) (i : Fin 3) :
    coneTernaryForms d τ ν V u a b i.castSucc = C (V i) * (C u * linearFormPolynomial τ) ^ d := by
  exact Fin.snoc_castSucc _ _ i

theorem coneTernaryForms_last (d : ℕ) (τ ν V : Fin 3 → F) (u a b : F) :
    coneTernaryForms d τ ν V u a b (Fin.last 3) =
      C a * (C u * linearFormPolynomial τ) ^ d +
        C b * (C u * linearFormPolynomial τ) ^ (d - 1) * linearFormPolynomial ν := by
  exact Fin.snoc_last _ _

/-- Every constructed entry has the original positive homogeneous
degree, including the mixed last-coordinate term. -/
theorem coneTernaryForms_homogeneous {d : ℕ} (hd : 0 < d)
    (τ ν V : Fin 3 → F) (u a b : F) :
    ∀ i : Fin 4, (coneTernaryForms d τ ν V u a b i).IsHomogeneous d := by
  have hR : (C u * linearFormPolynomial τ).IsHomogeneous 1 :=
    (linearFormPolynomial_homogeneous τ).C_mul u
  have hRd : ((C u * linearFormPolynomial τ) ^ d).IsHomogeneous d := by
    simpa only [one_mul] using hR.pow d
  have hRpred : ((C u * linearFormPolynomial τ) ^ (d - 1)).IsHomogeneous (d - 1) := by
    simpa only [one_mul] using hR.pow (d - 1)
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [coneTernaryForms_last]
    apply (hRd.C_mul a).add
    have he := (hRpred.C_mul b).mul (linearFormPolynomial_homogeneous ν)
    simpa only [Nat.sub_add_cancel hd] using he
  · rw [coneTernaryForms_castSucc]
    exact hRd.C_mul (V j)

variable {G : Type*} [Field G] [Algebra F G]

/-- Evaluation of all constructed forms agrees with the entire
fixed-vertex cone expression at its actual source point. -/
theorem coneTernaryForms_evaluate
    (d : ℕ) (τ ν V : Fin 3 → F) (u a b : F)
    (z : Fin 3 → G) (r : G)
    (hr : r = algebraMap F G u * (∑ i, algebraMap F G (τ i) * z i)) :
    (∀ i : Fin 3, aeval z (coneTernaryForms d τ ν V u a b i.castSucc) = algebraMap F G (V i) * r ^ d) ∧
      aeval z (coneTernaryForms d τ ν V u a b (Fin.last 3)) =
        algebraMap F G a * r ^ d +
          algebraMap F G b * r ^ (d - 1) * (∑ i, algebraMap F G (ν i) * z i) := by
  constructor
  · intro i
    rw [coneTernaryForms_castSucc]
    simp only [map_mul, map_pow, aeval_C, linearFormPolynomial, map_sum, aeval_X, ← hr]
  · rw [coneTernaryForms_last]
    simp only [map_add, map_mul, map_pow, aeval_C, linearFormPolynomial, map_sum, aeval_X, ← hr]

end DimensionFourDependence
