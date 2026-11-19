import DimensionFourDependence.ParametricStationarySquare

/-! # A stationary ruling constructs its actual finite scalar-times-linear-square form -/

namespace DimensionFourDependence

open Matrix

universe u
set_option maxHeartbeats 3000000

variable {K F : Type u} [Field K] [CharZero K] [Field F] [Algebra K F] {n : ℕ}

/-- The actual stationary ruling function of weight 2/d constructs
one finite extension of its original parameter field containing the
nonzero scalar and nonzero linear square factor. Its selected direction
is an exact zero of that same factor. -/
theorem parametric_stationary_weight_two_finite_linear_square_form
    (p : RatFunc K →ₐ[K] F) (δ : Fin n → Derivation K F F) (y v : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (hcomm : ∀ i j x, δ i (δ j x) = δ j (δ i x))
    (hv : v ≠ 0) (halg : ∀ i, IsAlgebraic p.fieldRange (v i))
    (htD : coordinateEuler v δ (p RatFunc.X) = 0)
    (htE : coordinateEuler y δ (p RatFunc.X) = 0)
    (htr : Algebra.trdeg K F ≤ 3) (d : ℕ) (hd : 0 < d)
    (f : F) (hf : f ≠ 0) (hDf : coordinateEuler v δ f = 0)
    (hweight : coordinateEuler y δ f = (2 * (d : F)⁻¹) * f) :
    ∃ C : IntermediateField p.fieldRange F, Module.Finite p.fieldRange C ∧
      ∃ (α : C) (S : Fin n → C), α ≠ 0 ∧ S ≠ 0 ∧
        f ^ d = (α : F) * ((fun i => (S i : F)) ⬝ᵥ y) ^ 2 ∧
        ((fun i => (S i : F)) ⬝ᵥ v) = 0 ∧ ((fun i => (S i : F)) ⬝ᵥ y) ≠ 0 := by
  classical
  obtain ⟨a, b, α, _ha, hs, hαalg, hα, hpower⟩ :=
    parametric_coordinate_stationary_weight_two_square p δ y v hcoord hcomm hv halg htD htE htr d hd f hf hDf hweight
  let R : Fin n → F := Pi.single a (v a)⁻¹
  let S : Fin n → F := Pi.single b 1 - v b • R
  have hR (i : Fin n) : IsAlgebraic p.fieldRange (R i) := by
    by_cases hi : i = a
    · subst i
      simpa only [R, Pi.single_eq_same] using (halg a).inv
    · rw [show R i = 0 from by simp [R, hi]]
      exact isAlgebraic_zero
  have hS (i : Fin n) : IsAlgebraic p.fieldRange (S i) := by
    have hsingle : IsAlgebraic p.fieldRange ((Pi.single b 1 : Fin n → F) i) := by
      by_cases hi : i = b
      · subst i; simpa only [Pi.single_eq_same] using (isAlgebraic_one : IsAlgebraic p.fieldRange (1 : F))
      · rw [show (Pi.single b 1 : Fin n → F) i = 0 from by simp [hi]]
        exact isAlgebraic_zero
    exact hsingle.sub ((halg b).mul (hR i))
  have hRy : R ⬝ᵥ y = y a / v a := by rw [show R = Pi.single a (v a)⁻¹ from rfl, single_dotProduct]; ring
  have hRv : R ⬝ᵥ v = 1 := by
    rw [show R = Pi.single a (v a)⁻¹ from rfl, single_dotProduct]
    exact inv_mul_cancel₀ _ha
  have hSy : S ⬝ᵥ y = y b - v b * (y a / v a) := by
    simp only [S, sub_dotProduct, smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul, hRy]
  have hSv : S ⬝ᵥ v = 0 := by
    simp only [S, sub_dotProduct, smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul, hRv, mul_one, sub_self]
  let C := IntermediateField.adjoin p.fieldRange (Set.range S ∪ ({α} : Set F))
  let : Fintype {x : F // x ∈ Set.range S ∪ ({α} : Set F)} :=
    ((Set.finite_range S).union (Set.finite_singleton α)).fintype
  have hfin : Module.Finite p.fieldRange C := IntermediateField.finiteDimensional_adjoin (by
    rintro x (⟨i, rfl⟩ | hx)
    · exact (hS i).isIntegral
    · rw [Set.mem_singleton_iff] at hx
      subst x
      exact hαalg.isIntegral)
  let S₀ : Fin n → C := fun i => ⟨S i, IntermediateField.subset_adjoin _ _ (Or.inl ⟨i, rfl⟩)⟩
  let α₀ : C := ⟨α, IntermediateField.subset_adjoin _ _ (Or.inr (by rfl))⟩
  refine ⟨C, hfin, α₀, S₀, ?_, ?_, ?_, hSv, ?_⟩
  · exact fun h => hα (congrArg Subtype.val h)
  · intro h
    have hz : S = 0 := funext (fun i => congrArg Subtype.val (congrFun h i))
    apply hs
    rw [← hSy, hz, zero_dotProduct]
  · rw [hSy]
    exact hpower
  · rw [hSy]
    exact hs

end DimensionFourDependence
