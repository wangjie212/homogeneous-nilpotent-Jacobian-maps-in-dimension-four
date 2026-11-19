import DimensionFourDependence.ParametricWeightedRulingFactorization

/-! # The actual weighted ruling function gives the linear forms in (4.4)

The explicit longitudinal and transverse coordinates give original
linear covectors m and s with f=m(y)rho, rho^d=s(y), and s(v)=0.
Every coefficient is algebraic over the actual parameter image. All
coefficients can therefore be placed in one finite extension of it.
-/

namespace DimensionFourDependence

open Matrix

universe u

variable {K F : Type u} [Field K] [CharZero K] [Field F] [Algebra K F] {n : ℕ}

/-- The actual weighted ruling function constructs two nonzero
original linear forms and the root identity (4.4), with parameter-algebraic
coefficients and the transverse form vanishing on the given direction. -/
theorem parametric_weighted_function_linear_root_forms
    (p : RatFunc K →ₐ[K] F) (δ : Fin n → Derivation K F F) (y v : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (hcomm : ∀ i j x, δ i (δ j x) = δ j (δ i x))
    (hv : v ≠ 0) (halg : ∀ i, IsAlgebraic p.fieldRange (v i))
    (htD : coordinateEuler v δ (p RatFunc.X) = 0)
    (htE : coordinateEuler y δ (p RatFunc.X) = 0)
    (htr : Algebra.trdeg K F ≤ 3) {d : ℕ} (hd : 0 < d)
    (f : F) (hf : f ≠ 0) (hsecond : coordinateEuler v δ (coordinateEuler v δ f) = 0)
    (hweight : coordinateEuler y δ f = (1 + (d : F)⁻¹) * f) :
    ∃ (m s : Fin n → F) (ρ : F),
      (∀ i, IsAlgebraic p.fieldRange (m i) ∧ IsAlgebraic p.fieldRange (s i)) ∧
      m ≠ 0 ∧ s ≠ 0 ∧ ρ ≠ 0 ∧ f = (m ⬝ᵥ y) * ρ ∧ ρ ^ d = s ⬝ᵥ y ∧ s ⬝ᵥ v = 0 ∧
      coordinateEuler v δ ρ = 0 := by
  classical
  obtain ⟨a, b, α, β, γ, ρ, ha, hs, hα, hβ, hγ, hα0, hρ, hfactor, hroot, hρD, _⟩ :=
    parametric_coordinate_weighted_root_factorization p δ y v hcoord hcomm hv halg htD htE htr hd f hf hsecond hweight
  let R : Fin n → F := Pi.single a (v a)⁻¹
  let S : Fin n → F := Pi.single b 1 - v b • R
  let m : Fin n → F := β • R + γ • S
  let s : Fin n → F := α • S
  have hR (i : Fin n) : IsAlgebraic p.fieldRange (R i) := by
    by_cases hi : i = a
    · subst i
      simpa only [R, Pi.single_eq_same] using (halg a).inv
    · have he : R i = 0 := by simp [R, hi]
      rw [he]
      exact isAlgebraic_zero
  have hS (i : Fin n) : IsAlgebraic p.fieldRange (S i) := by
    have hsingle : IsAlgebraic p.fieldRange ((Pi.single b 1 : Fin n → F) i) := by
      by_cases hi : i = b
      · subst i
        simp only [Pi.single_eq_same]
        exact isAlgebraic_one
      · have he : (Pi.single b 1 : Fin n → F) i = 0 := by simp [hi]
        rw [he]
        exact isAlgebraic_zero
    exact hsingle.sub ((halg b).mul (hR i))
  have hRy : R ⬝ᵥ y = y a / v a := by
    rw [show R = Pi.single a (v a)⁻¹ from rfl, single_dotProduct]
    ring
  have hRv : R ⬝ᵥ v = 1 := by
    rw [show R = Pi.single a (v a)⁻¹ from rfl, single_dotProduct]
    exact inv_mul_cancel₀ ha
  have hSy : S ⬝ᵥ y = y b - v b * (y a / v a) := by
    simp only [S, sub_dotProduct, smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul, hRy]
  have hSv : S ⬝ᵥ v = 0 := by
    simp only [S, sub_dotProduct, smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul, hRv, mul_one, sub_self]
  have hmy : m ⬝ᵥ y = β * (y a / v a) + γ * (y b - v b * (y a / v a)) := by
    simp only [m, add_dotProduct, smul_dotProduct, smul_eq_mul, hRy, hSy]
  have hsy : s ⬝ᵥ y = α * (y b - v b * (y a / v a)) := by
    simp only [s, smul_dotProduct, smul_eq_mul, hSy]
  have hfactor' : f = (m ⬝ᵥ y) * ρ := by rw [hmy]; exact hfactor
  have hroot' : ρ ^ d = s ⬝ᵥ y := by rw [hsy]; exact hroot
  refine ⟨m, s, ρ, fun i => ⟨(hβ.mul (hR i)).add (hγ.mul (hS i)), hα.mul (hS i)⟩,
    ?_, ?_, hρ, hfactor', hroot', ?_, hρD⟩
  · intro hm
    rw [hm, zero_dotProduct, zero_mul] at hfactor'
    exact hf hfactor'
  · intro hz
    rw [hz, zero_dotProduct] at hroot'
    exact (pow_ne_zero d hρ) hroot'
  · simp only [s, smul_dotProduct, smul_eq_mul, hSv, mul_zero]

/-- All actual linear-form coefficients in (4.4) lie in one
constructed finite extension of the actual Gauss-parameter image. -/
theorem parametric_weighted_function_finite_linear_root_forms
    (p : RatFunc K →ₐ[K] F) (δ : Fin n → Derivation K F F) (y v : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (hcomm : ∀ i j x, δ i (δ j x) = δ j (δ i x))
    (hv : v ≠ 0) (halg : ∀ i, IsAlgebraic p.fieldRange (v i))
    (htD : coordinateEuler v δ (p RatFunc.X) = 0)
    (htE : coordinateEuler y δ (p RatFunc.X) = 0)
    (htr : Algebra.trdeg K F ≤ 3) {d : ℕ} (hd : 0 < d)
    (f : F) (hf : f ≠ 0) (hsecond : coordinateEuler v δ (coordinateEuler v δ f) = 0)
    (hweight : coordinateEuler y δ f = (1 + (d : F)⁻¹) * f) :
    ∃ C : IntermediateField p.fieldRange F, Module.Finite p.fieldRange C ∧
      ∃ (m s : Fin n → C) (ρ : F), m ≠ 0 ∧ s ≠ 0 ∧ ρ ≠ 0 ∧
        f = ((fun i => (m i : F)) ⬝ᵥ y) * ρ ∧
        ρ ^ d = (fun i => (s i : F)) ⬝ᵥ y ∧ (fun i => (s i : F)) ⬝ᵥ v = 0 ∧
        coordinateEuler v δ ρ = 0 := by
  classical
  obtain ⟨m, s, ρ, halg', hm, hs, hρ, hfactor, hroot, hsv, hρD⟩ :=
    parametric_weighted_function_linear_root_forms p δ y v hcoord hcomm hv halg htD htE htr hd f hf hsecond hweight
  let C := IntermediateField.adjoin p.fieldRange (Set.range m ∪ Set.range s)
  let : Fintype {x : F // x ∈ Set.range m ∪ Set.range s} :=
    ((Set.finite_range m).union (Set.finite_range s)).fintype
  have hfin : Module.Finite p.fieldRange C := IntermediateField.finiteDimensional_adjoin (by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact (halg' i).1.isIntegral
    · exact (halg' i).2.isIntegral)
  let m₀ : Fin n → C := fun i => ⟨m i, IntermediateField.subset_adjoin _ _ (Or.inl ⟨i, rfl⟩)⟩
  let s₀ : Fin n → C := fun i => ⟨s i, IntermediateField.subset_adjoin _ _ (Or.inr ⟨i, rfl⟩)⟩
  refine ⟨C, hfin, m₀, s₀, ρ, ?_, ?_, hρ, hfactor, hroot, hsv, hρD⟩
  · intro hz
    exact hm (funext (fun i => congrArg Subtype.val (congrFun hz i)))
  · intro hz
    exact hs (funext (fun i => congrArg Subtype.val (congrFun hz i)))

end DimensionFourDependence
