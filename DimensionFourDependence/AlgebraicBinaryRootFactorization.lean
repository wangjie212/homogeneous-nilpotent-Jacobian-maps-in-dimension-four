import DimensionFourDependence.WeightedAffineRootFactorization
import DimensionFourDependence.EulerDerivation

/-! # Constructed root factorization for actual algebraic binary functions

The uniquely extended coordinate derivations supply the surface dimension,
Euler commutator and normalized direction coordinates internally.
-/

namespace DimensionFourDependence

universe u

variable {K F : Type u} [Field K] [CharZero K] [Field F]
  [Algebra (FractionRing (MvPolynomial (Fin 2) K)) F] [Algebra K F]
  [IsScalarTower K (FractionRing (MvPolynomial (Fin 2) K)) F]
  [Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin 2) K)) F]

local notation "R₀" => FractionRing (MvPolynomial (Fin 2) K)
local notation "y" => fun i : Fin 2 => algebraMap R₀ F (rationalCoordinate (K := K) i)
local notation "δ" => algebraicPartial (K := K) (n := 2) F
local notation "ε" => coordinateEuler (y) (δ)

/-- The actual algebraic binary Euler derivation gives weight one
to each original binary coordinate. -/
theorem algebraic_binary_euler_coordinate (i : Fin 2) : (ε) ((y) i) = (y) i := by
  rw [coordinateEuler_apply]
  simp only [algebraicPartial_coordinate]
  simp [apply_ite]

/-- Every nonzero algebraic binary function of Euler weight 1+1/d
whose actual first-coordinate second derivative vanishes is a binary
linear form times a root of a nonzero scalar multiple of the second
coordinate. All three linear coefficients are algebraic over the base.
No constants, root, dimension bound or derivative commutator are supplied. -/
theorem algebraic_binary_function_root_factorization {d : ℕ} (hd : 0 < d)
    (f : F) (hf : f ≠ 0) (hsecond : (δ) 0 ((δ) 0 f) = 0)
    (hweight : (ε) f = (1 + (d : F)⁻¹) * f) :
    ∃ α β γ ρ : F, IsAlgebraic K α ∧ IsAlgebraic K β ∧ IsAlgebraic K γ ∧
      α ≠ 0 ∧ ρ ≠ 0 ∧ f = (β * (y) 0 + γ * (y) 1) * ρ ∧
      ρ ^ d = α * (y) 1 ∧ (δ) 0 ρ = 0 ∧ (β ≠ 0 ∨ γ ≠ 0) := by
  have hcoord : ∀ i j, (δ) i ((y) j) = if j = i then 1 else 0 :=
    algebraicPartial_coordinate F
  have hs : (y) 1 ≠ 0 := by
    intro hz
    have he := congrArg ((δ) 1) hz
    simp [hcoord] at he
  have htr : Algebra.trdeg K F ≤ 2 := by
    have he := trdeg_add_eq (A := F) K R₀
    rw [show Algebra.trdeg R₀ F = 0 from trdeg_eq_zero, add_zero] at he
    exact he.symm.le.trans (rationalSource_trdeg_le (K := K) (n := 2))
  exact weighted_affine_function_root_factorization ((δ) 0) (ε) ((y) 0) ((y) 1)
    (by simpa using hcoord 0 0) (algebraic_binary_euler_coordinate 0)
    (by simpa using hcoord 0 1) (algebraic_binary_euler_coordinate 1) hs
    (coordinatePartial_euler (y) (δ) hcoord (algebraicPartials_commute F) 0)
    htr hd f hf hsecond hweight

/-- The constructed algebraic coefficients all belong to one actual
finite extension of the ruling field, retaining the original function
and the exact root and factorization equations in the ambient field. -/
theorem algebraic_binary_function_root_factorization_finite_coefficients {d : ℕ} (hd : 0 < d)
    (f : F) (hf : f ≠ 0) (hsecond : (δ) 0 ((δ) 0 f) = 0)
    (hweight : (ε) f = (1 + (d : F)⁻¹) * f) :
    ∃ C : IntermediateField K F, Module.Finite K C ∧
      ∃ (α β γ : C) (ρ : F), α ≠ 0 ∧ ρ ≠ 0 ∧
        f = ((β : F) * (y) 0 + (γ : F) * (y) 1) * ρ ∧
        ρ ^ d = (α : F) * (y) 1 ∧ (δ) 0 ρ = 0 ∧ (β ≠ 0 ∨ γ ≠ 0) := by
  obtain ⟨α, β, γ, ρ, hα, hβ, hγ, hα0, hρ, hfactor, hroot, hρD, hlinear⟩ :=
    algebraic_binary_function_root_factorization hd f hf hsecond hweight
  let C := IntermediateField.adjoin K ({α, β, γ} : Set F)
  have hfin : Module.Finite K C := IntermediateField.finiteDimensional_adjoin (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hα.isIntegral
    · exact hβ.isIntegral
    · exact hγ.isIntegral)
  let α₀ : C := ⟨α, IntermediateField.subset_adjoin K _ (by simp)⟩
  let β₀ : C := ⟨β, IntermediateField.subset_adjoin K _ (by simp)⟩
  let γ₀ : C := ⟨γ, IntermediateField.subset_adjoin K _ (by simp)⟩
  refine ⟨C, hfin, α₀, β₀, γ₀, ρ, ?_, hρ, hfactor, hroot, hρD, ?_⟩
  · intro hz
    exact hα0 (congrArg Subtype.val hz)
  · rcases hlinear with hb | hc
    · exact Or.inl (fun hz => hb (congrArg Subtype.val hz))
    · exact Or.inr (fun hz => hc (congrArg Subtype.val hz))

end DimensionFourDependence
